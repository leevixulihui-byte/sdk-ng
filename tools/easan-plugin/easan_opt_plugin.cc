#include "gcc-plugin.h"
#include "plugin-version.h"
#include "context.h"
#include "function.h"
#include "tree.h"
#include "tree-pass.h"
#include "basic-block.h"
#include "gimple.h"
#include "gimple-iterator.h"
#include "gimple-ssa.h"
#include "stringpool.h"
#include "attribs.h"
#include "diagnostic-core.h"
#include "input.h"

#include <cstdint>
#include <cstdio>
#include <cstring>

#ifdef _WIN32
#define EASAN_PLUGIN_EXPORT __declspec(dllexport)
#else
#define EASAN_PLUGIN_EXPORT
#endif

extern "C" EASAN_PLUGIN_EXPORT int plugin_is_GPL_compatible;
int plugin_is_GPL_compatible;

namespace {

constexpr const char *kPluginVersion = "0.1.0";

struct plugin_options {
    bool strict = true;
    bool quiet = false;
};

plugin_options options;

const pass_data memop_pass_data = {
    GIMPLE_PASS, "easan_memop_v1", OPTGROUP_NONE, TV_NONE,
    PROP_ssa, 0, 0, 0, 0,
};

const pass_data callback_pass_data = {
    GIMPLE_PASS, "easan_callback_v1", OPTGROUP_NONE, TV_NONE,
    PROP_ssa, 0, 0, 0, 0,
};

const char *decl_name(tree decl)
{
    if (decl == nullptr || DECL_NAME(decl) == nullptr) {
        return nullptr;
    }
    return IDENTIFIER_POINTER(DECL_NAME(decl));
}

const char *function_name(function *fn)
{
    const char *name = decl_name(fn != nullptr ? fn->decl : nullptr);
    return name != nullptr ? name : "<unknown>";
}

tree external_decl(const char *name, tree function_type, tree original = nullptr)
{
    tree decl = build_fn_decl(name, function_type);
    TREE_PUBLIC(decl) = 1;
    DECL_EXTERNAL(decl) = 1;
    DECL_ARTIFICIAL(decl) = 1;
    if (original != nullptr) {
        TREE_NOTHROW(decl) = TREE_NOTHROW(original);
    }
    return decl;
}

enum class memop_kind {
    none,
    memcpy,
    memmove,
    memset,
};

memop_kind classify_memop(const char *name)
{
    if (name == nullptr) {
        return memop_kind::none;
    }
    if (std::strcmp(name, "memcpy") == 0 || std::strcmp(name, "__builtin_memcpy") == 0) {
        return memop_kind::memcpy;
    }
    if (std::strcmp(name, "memmove") == 0 || std::strcmp(name, "__builtin_memmove") == 0) {
        return memop_kind::memmove;
    }
    if (std::strcmp(name, "memset") == 0 || std::strcmp(name, "__builtin_memset") == 0) {
        return memop_kind::memset;
    }
    return memop_kind::none;
}

const char *pending_name(memop_kind kind)
{
    switch (kind) {
    case memop_kind::memcpy:
        return "__easan_pending_memcpy_v1";
    case memop_kind::memmove:
        return "__easan_pending_memmove_v1";
    case memop_kind::memset:
        return "__easan_pending_memset_v1";
    default:
        return nullptr;
    }
}

const char *final_name(memop_kind kind)
{
    switch (kind) {
    case memop_kind::memcpy:
        return "__easan_memcpy_v1";
    case memop_kind::memmove:
        return "__easan_memmove_v1";
    case memop_kind::memset:
        return "__easan_memset_v1";
    default:
        return nullptr;
    }
}

memop_kind classify_pending(const char *name)
{
    for (memop_kind kind : { memop_kind::memcpy, memop_kind::memmove, memop_kind::memset }) {
        if (name != nullptr && std::strcmp(name, pending_name(kind)) == 0) {
            return kind;
        }
    }
    return memop_kind::none;
}

uint32_t fnv1a_update(uint32_t hash, const char *text)
{
    if (text == nullptr) {
        return hash;
    }
    for (const unsigned char *p = reinterpret_cast<const unsigned char *>(text); *p != 0; ++p) {
        hash ^= *p;
        hash *= 16777619U;
    }
    return hash;
}

uint32_t site_id(function *fn, location_t location)
{
    expanded_location expanded = expand_location(location);
    uint32_t hash = 2166136261U;
    hash = fnv1a_update(hash, expanded.file);
    hash = fnv1a_update(hash, function_name(fn));
    hash ^= static_cast<uint32_t>(expanded.line);
    hash *= 16777619U;
    hash ^= static_cast<uint32_t>(expanded.column);
    hash *= 16777619U;
    return hash == 0U ? 1U : hash;
}

tree rewrite_frontend_memop(tree *node_ptr, int *, void *data)
{
    tree node = *node_ptr;
    if (node == nullptr || TREE_CODE(node) != CALL_EXPR) {
        return nullptr;
    }

    tree original = get_callee_fndecl(node);
    memop_kind kind = classify_memop(decl_name(original));
    if (kind == memop_kind::none) {
        return nullptr;
    }

    tree pending = external_decl(pending_name(kind), TREE_TYPE(original), original);
    CALL_EXPR_FN(node) = build_fold_addr_expr(pending);
    ++*static_cast<unsigned *>(data);
    return nullptr;
}

bool instrumentation_disabled(tree decl)
{
    if (decl == nullptr) {
        return false;
    }
    tree attributes = DECL_ATTRIBUTES(decl);
    return lookup_attribute("no_sanitize_address", attributes) != nullptr
        || lookup_attribute("no_address_safety_analysis", attributes) != nullptr
        || lookup_attribute("no_sanitize", attributes) != nullptr;
}

void finish_parse_function(void *event_data, void *)
{
    tree fn = static_cast<tree>(event_data);
    if (fn == nullptr || DECL_SAVED_TREE(fn) == nullptr || instrumentation_disabled(fn)) {
        return;
    }

    unsigned rewritten = 0;
    walk_tree_without_duplicates(&DECL_SAVED_TREE(fn), rewrite_frontend_memop, &rewritten);
    if (!options.quiet && rewritten != 0U) {
        std::fprintf(stderr, "EASAN_MANIFEST phase=frontend function=%s memops=%u\n",
                     decl_name(fn), rewritten);
    }
}

tree final_memop_decl(memop_kind kind, gcall *call)
{
    tree argument_types[4];
    for (unsigned i = 0; i < 3; ++i) {
        argument_types[i] = TREE_TYPE(gimple_call_arg(call, i));
    }
    argument_types[3] = uint32_type_node;
    tree original = gimple_call_fndecl(call);
    tree return_type = TREE_TYPE(TREE_TYPE(original));
    tree function_type = build_function_type_array(return_type, 4, argument_types);
    return external_decl(final_name(kind), function_type, original);
}

class easan_memop_pass final : public gimple_opt_pass {
public:
    explicit easan_memop_pass(gcc::context *context)
        : gimple_opt_pass(memop_pass_data, context)
    {
    }

    unsigned int execute(function *fn) final
    {
        if (instrumentation_disabled(fn != nullptr ? fn->decl : nullptr)) {
            return 0;
        }
        unsigned rewritten = 0;
        basic_block bb;
        FOR_EACH_BB_FN(bb, fn) {
            for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi);) {
                gimple *stmt = gsi_stmt(gsi);
                if (!is_gimple_call(stmt)) {
                    gsi_next(&gsi);
                    continue;
                }

                gcall *old_call = as_a<gcall *>(stmt);
                memop_kind kind = classify_pending(decl_name(gimple_call_fndecl(old_call)));
                if (kind == memop_kind::none) {
                    gsi_next(&gsi);
                    continue;
                }
                if (gimple_call_num_args(old_call) != 3U) {
                    error_at(gimple_location(old_call), "EASan memory operation requires exactly three arguments");
                    gsi_next(&gsi);
                    continue;
                }

                location_t location = gimple_location(old_call);
                tree id = build_int_cst(uint32_type_node, site_id(fn, location));
                gcall *new_call = gimple_build_call(final_memop_decl(kind, old_call), 4,
                                                    gimple_call_arg(old_call, 0),
                                                    gimple_call_arg(old_call, 1),
                                                    gimple_call_arg(old_call, 2), id);
                gimple_call_set_lhs(new_call, gimple_call_lhs(old_call));
                gimple_set_location(new_call, location);
                gsi_replace(&gsi, new_call, true);
                ++rewritten;
                gsi_next(&gsi);
            }
        }

        if (!options.quiet && rewritten != 0U) {
            std::fprintf(stderr, "EASAN_MANIFEST phase=memop function=%s normalized=%u\n",
                         function_name(fn), rewritten);
        }
        return rewritten != 0U ? TODO_update_ssa : 0U;
    }
};

const char *easan_store_name(const char *name)
{
    if (name == nullptr) {
        return nullptr;
    }
    if (std::strstr(name, "asan_store16") != nullptr) {
        return "__easan_store16";
    }
    if (std::strstr(name, "asan_store8") != nullptr) {
        return "__easan_store8";
    }
    if (std::strstr(name, "asan_store4") != nullptr) {
        return "__easan_store4";
    }
    if (std::strstr(name, "asan_store2") != nullptr) {
        return "__easan_store2";
    }
    if (std::strstr(name, "asan_store1") != nullptr) {
        return "__easan_store1";
    }
    return nullptr;
}

bool is_hot_function(function *fn)
{
    return fn != nullptr && fn->decl != nullptr
        && lookup_attribute("easan_hot", DECL_ATTRIBUTES(fn->decl)) != nullptr;
}

class easan_callback_pass final : public gimple_opt_pass {
public:
    explicit easan_callback_pass(gcc::context *context)
        : gimple_opt_pass(callback_pass_data, context)
    {
    }

    unsigned int execute(function *fn) final
    {
        if (instrumentation_disabled(fn != nullptr ? fn->decl : nullptr)) {
            return 0;
        }
        unsigned stores = 0;
        unsigned loads = 0;
        basic_block bb;
        FOR_EACH_BB_FN(bb, fn) {
            for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
                gimple *stmt = gsi_stmt(gsi);
                if (!is_gimple_call(stmt)) {
                    continue;
                }
                gcall *call = as_a<gcall *>(stmt);
                tree original = gimple_call_fndecl(call);
                const char *name = decl_name(original);
                if (name == nullptr) {
                    continue;
                }
                if (std::strstr(name, "asan_load") != nullptr) {
                    ++loads;
                    continue;
                }
                const char *replacement = easan_store_name(name);
                if (replacement != nullptr) {
                    gimple_call_set_fndecl(call, external_decl(replacement, TREE_TYPE(original), original));
                    update_stmt(stmt);
                    ++stores;
                }
            }
        }

        if (loads != 0U && options.strict) {
            error_at(DECL_SOURCE_LOCATION(fn->decl),
                     "EASan write-only build contains %u scalar ASan load callback(s)", loads);
        }
        if (!options.quiet && (stores != 0U || loads != 0U || is_hot_function(fn))) {
            std::fprintf(stderr,
                         "EASAN_MANIFEST phase=callbacks function=%s hot=%u stores=%u loads=%u\n",
                         function_name(fn), is_hot_function(fn) ? 1U : 0U, stores, loads);
        }
        return 0;
    }
};

const attribute_spec easan_hot_attribute = {
    "easan_hot", 0, 0, true, false, false, false, nullptr, nullptr,
};

const attribute_spec easan_no_layout_attribute = {
    "no_easan_layout", 0, 0, true, false, false, false, nullptr, nullptr,
};

void register_attributes(void *, void *)
{
    register_attribute(&easan_hot_attribute);
    register_attribute(&easan_no_layout_attribute);
}

bool parse_boolean(const char *value, bool default_value)
{
    if (value == nullptr) {
        return default_value;
    }
    if (std::strcmp(value, "1") == 0 || std::strcmp(value, "true") == 0 || std::strcmp(value, "yes") == 0) {
        return true;
    }
    if (std::strcmp(value, "0") == 0 || std::strcmp(value, "false") == 0 || std::strcmp(value, "no") == 0) {
        return false;
    }
    return default_value;
}

void parse_options(const plugin_name_args *plugin_info)
{
    for (int i = 0; i < plugin_info->argc; ++i) {
        const plugin_argument &argument = plugin_info->argv[i];
        if (std::strcmp(argument.key, "strict") == 0) {
            options.strict = parse_boolean(argument.value, true);
        } else if (std::strcmp(argument.key, "quiet") == 0) {
            options.quiet = parse_boolean(argument.value, true);
        }
    }
}

} // namespace

extern "C" EASAN_PLUGIN_EXPORT int
plugin_init(plugin_name_args *plugin_info, plugin_gcc_version *version)
{
    if (!plugin_default_version_check(version, &gcc_version)) {
        std::fprintf(stderr, "EASAN_PLUGIN version_mismatch plugin=%s\n", kPluginVersion);
        return 1;
    }

    parse_options(plugin_info);

    static struct plugin_info info = {
        kPluginVersion,
        "EASan lightweight optimization extension",
    };
    register_callback(plugin_info->base_name, PLUGIN_INFO, nullptr, &info);
    register_callback(plugin_info->base_name, PLUGIN_ATTRIBUTES, register_attributes, nullptr);
    register_callback(plugin_info->base_name, PLUGIN_FINISH_PARSE_FUNCTION, finish_parse_function, nullptr);

    static register_pass_info memop_pass;
    memop_pass.pass = new easan_memop_pass(g);
    memop_pass.reference_pass_name = "ssa";
    memop_pass.ref_pass_instance_number = 1;
    memop_pass.pos_op = PASS_POS_INSERT_AFTER;
    register_callback(plugin_info->base_name, PLUGIN_PASS_MANAGER_SETUP, nullptr, &memop_pass);

    static register_pass_info callback_pass;
    callback_pass.pass = new easan_callback_pass(g);
    callback_pass.reference_pass_name = "sanopt";
    callback_pass.ref_pass_instance_number = 1;
    callback_pass.pos_op = PASS_POS_INSERT_AFTER;
    register_callback(plugin_info->base_name, PLUGIN_PASS_MANAGER_SETUP, nullptr, &callback_pass);

    if (!options.quiet) {
        std::fprintf(stderr, "EASAN_PLUGIN loaded version=%s strict=%u\n",
                     kPluginVersion, options.strict ? 1U : 0U);
    }
    return 0;
}
