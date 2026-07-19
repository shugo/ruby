#ifndef PRISM_PARSEY_YID_H
#define PRISM_PARSEY_YID_H

#include "prism/internal/arena.h"
#include "prism/internal/constant_pool.h"
#include "prism/internal/encoding.h"

#include <stdbool.h>
#include <stdint.h>

/*
 * The grammar forked from CRuby's parse.y identifies names with CRuby's ID
 * type: an integer that encodes both which name it is and what kind of name it
 * is (local, constant, instance variable, ...). The grammar and the lexer lean
 * on that encoding constantly -- `is_local_id(id)`, `id_type(id)`,
 * `rb_id_attrset(id)` -- so rather than replace the concept, this reproduces
 * CRuby's bit layout exactly and only swaps out what sits underneath it: where
 * CRuby resolves the name half of an ID through its global symbol table, this
 * resolves it through the prism parser's constant pool. Keeping the layout
 * identical is what lets the ported code keep its CRuby form.
 *
 * An ID is laid out as in CRuby's id.h:
 *
 *     (serial << ID_SCOPE_SHIFT) | type | ID_STATIC_SYM
 *
 * with three regions of `serial`, in increasing order:
 *
 *   - Operator IDs (`+`, `<=>`, `[]=`, ...). These are not encoded at all: the
 *     ID *is* the token value, which is why they are all <= PM_YID_LAST_OP_ID
 *     and why `is_notop_id` is a plain comparison. Their names come from
 *     pm_yid_op_name().
 *   - Static IDs, the names the grammar refers to by C constant rather than by
 *     text. Their serials are token values from CRuby's id.h.
 *   - Dynamic IDs, every name that comes from the source. Their serials are
 *     prism constant pool ids, biased past the static region.
 */
typedef uint32_t pm_yid_t;

/*
 * The kind of name an ID holds, in the low bits of the ID. These values are
 * CRuby's `enum ruby_id_types` and must not be renumbered: the ported grammar
 * and lexer compare against them.
 */
enum pm_yid_types {
    PM_YID_LOCAL       = 0x00,
    PM_YID_STATIC_SYM  = 0x01,
    PM_YID_INSTANCE    = (0x01 << 1),
    PM_YID_GLOBAL      = (0x03 << 1),
    PM_YID_ATTRSET     = (0x04 << 1),
    PM_YID_CONST       = (0x05 << 1),
    PM_YID_CLASS       = (0x06 << 1),
    PM_YID_INTERNAL    = (0x07 << 1),
    PM_YID_SCOPE_SHIFT = 4,
    PM_YID_SCOPE_MASK  = (~(~0U << (PM_YID_SCOPE_SHIFT - 1)) << 1)
};

/*
 * The largest ID that is an operator rather than an encoded name, and the
 * largest serial reserved for the static IDs above it. Both come from CRuby's
 * id.h, where they are derived from the token numbering.
 */
#define PM_YID_LAST_OP_ID 171
#define PM_YID_LAST_STATIC_SERIAL 255

/*
 * The bias applied to a prism constant pool id to get the serial of a dynamic
 * ID. Constant pool ids start at 1, so without this the first name interned
 * would land in the operator ID range and `is_notop_id` would misclassify it.
 */
#define PM_YID_DYNAMIC_SERIAL_BASE (PM_YID_LAST_STATIC_SERIAL + 1)

/* Whether the given ID encodes a name rather than being an operator token. */
#define pm_yid_is_notop(id) ((id) > PM_YID_LAST_OP_ID)

/*
 * The kind of name the given ID holds. Operator IDs have no type bits of their
 * own and are all considered locals, which is what CRuby does.
 */
static inline int
pm_yid_type(pm_yid_t id) {
    if (pm_yid_is_notop(id)) return (int) (id & PM_YID_SCOPE_MASK);
    return PM_YID_LOCAL;
}

#define pm_yid_is_local(id)    (pm_yid_type(id) == PM_YID_LOCAL)
#define pm_yid_is_instance(id) (pm_yid_type(id) == PM_YID_INSTANCE)
#define pm_yid_is_global(id)   (pm_yid_type(id) == PM_YID_GLOBAL)
#define pm_yid_is_const(id)    (pm_yid_type(id) == PM_YID_CONST)
#define pm_yid_is_class(id)    (pm_yid_type(id) == PM_YID_CLASS)
#define pm_yid_is_attrset(id)  (pm_yid_type(id) == PM_YID_ATTRSET)
#define pm_yid_is_internal(id) (pm_yid_type(id) == PM_YID_INTERNAL)

/* The ID that is not any name at all. CRuby spells this 0. */
#define PM_YID_NULL ((pm_yid_t) 0)

/*
 * Intern the given name into the constant pool and return the ID for it. The
 * kind of the ID is derived from the bytes of the name, exactly as CRuby's
 * rb_intern does, so that `x`, `@x`, `$x`, `X` and `x=` all produce IDs that
 * the ported grammar can classify without being told which it asked for.
 *
 * The name is not required to outlive the call: it is copied into the arena if
 * it is not already interned.
 */
pm_yid_t pm_yid_intern(pm_arena_t *arena, pm_constant_pool_t *pool, const uint8_t *name, size_t length, const pm_encoding_t *encoding);

/*
 * The constant pool id for the name of the given ID, interning it if needed.
 * This is the bridge from the grammar's IDs to the constant ids that prism's
 * nodes hold: an operator ID's name has to be interned on demand, since it was
 * never in the pool to begin with, while a dynamic ID's name is already there
 * and only needs unbiasing.
 */
pm_constant_id_t pm_yid_to_constant(pm_arena_t *arena, pm_constant_pool_t *pool, pm_yid_t id);

/*
 * The name of an operator ID, or NULL if the given ID is not an operator. The
 * returned string is static and NUL-terminated.
 */
const char * pm_yid_op_name(pm_yid_t id);

/*
 * The ID for the attribute writer corresponding to the given ID, e.g. `x` to
 * `x=`. Mirrors CRuby's rb_id_attrset for the cases the grammar uses it in.
 */
pm_yid_t pm_yid_attrset(pm_arena_t *arena, pm_constant_pool_t *pool, pm_yid_t id);

#endif
