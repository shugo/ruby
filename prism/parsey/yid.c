#include "yid.h"

#include <string.h>

/*
 * The operator IDs, as CRuby's id.h numbers them. Only the ones whose value is
 * not simply the character itself need naming here; the rest are handled by
 * pm_yid_op_name() falling through to the single-character case.
 *
 * These values are RUBY_TOKEN_* from CRuby's id.h and must not be renumbered:
 * the ported grammar produces them directly from token values.
 */
typedef struct {
    pm_yid_t id;
    const char *name;
} pm_yid_op_t;

static const pm_yid_op_t pm_yid_ops[] = {
    { 128, ".."  }, /* RUBY_TOKEN_DOT2 */
    { 129, "..." }, /* RUBY_TOKEN_DOT3 */
    { 130, ".."  }, /* RUBY_TOKEN_BDOT2 */
    { 131, "..." }, /* RUBY_TOKEN_BDOT3 */
    { 132, "+@"  }, /* RUBY_TOKEN_UPLUS */
    { 133, "-@"  }, /* RUBY_TOKEN_UMINUS */
    { 134, "**"  }, /* RUBY_TOKEN_POW */
    { 135, "<=>" }, /* RUBY_TOKEN_CMP */
    { 136, "<<"  }, /* RUBY_TOKEN_LSHFT */
    { 137, ">>"  }, /* RUBY_TOKEN_RSHFT */
    { 138, "<="  }, /* RUBY_TOKEN_LEQ */
    { 139, ">="  }, /* RUBY_TOKEN_GEQ */
    { 140, "=="  }, /* RUBY_TOKEN_EQ */
    { 141, "===" }, /* RUBY_TOKEN_EQQ */
    { 142, "!="  }, /* RUBY_TOKEN_NEQ */
    { 143, "=~"  }, /* RUBY_TOKEN_MATCH */
    { 144, "!~"  }, /* RUBY_TOKEN_NMATCH */
    { 145, "[]"  }, /* RUBY_TOKEN_AREF */
    { 146, "[]=" }, /* RUBY_TOKEN_ASET */
    { 147, "::"  }, /* RUBY_TOKEN_COLON2 */
    { 148, "&&"  }, /* RUBY_TOKEN_ANDOP */
    { 149, "||"  }, /* RUBY_TOKEN_OROP */
    { 150, "&."  }  /* RUBY_TOKEN_ANDDOT */
};

const char *
pm_yid_op_name(pm_yid_t id) {
    if (!pm_yid_is_notop(id)) {
        for (size_t index = 0; index < sizeof(pm_yid_ops) / sizeof(pm_yid_op_t); index++) {
            if (pm_yid_ops[index].id == id) return pm_yid_ops[index].name;
        }

        /* The remaining operator IDs are the character itself, e.g. idPLUS is
         * '+'. Return a pointer into a table of one-character strings so that
         * callers can treat every operator name uniformly. */
        static const char pm_yid_op_chars[128][2] = {
#define C(n) [n] = { (char) (n), '\0' }
            C(0x21), C(0x25), C(0x26), C(0x2a), C(0x2b), C(0x2d), C(0x2f),
            C(0x3c), C(0x3e), C(0x5e), C(0x60), C(0x7c), C(0x7e)
#undef C
        };

        if (id < 128 && pm_yid_op_chars[id][0] != '\0') return pm_yid_op_chars[id];
    }

    return NULL;
}

/*
 * Classify a name by its bytes, the way CRuby's rb_enc_symname_type does for
 * the subset of names the parser interns. The parser only ever hands us names
 * that its own lexer accepted, so this does not have to reject malformed ones;
 * it only has to agree with the lexer about which kind each is.
 */
static int
pm_yid_type_for(const uint8_t *name, size_t length, const pm_encoding_t *encoding) {
    if (length == 0) return PM_YID_LOCAL;

    switch (name[0]) {
        case '$':
            return PM_YID_GLOBAL;
        case '@':
            return (length > 1 && name[1] == '@') ? PM_YID_CLASS : PM_YID_INSTANCE;
        default:
            break;
    }

    /* A trailing `=` that is not part of an operator name makes this a writer,
     * e.g. `x=`. `==`, `<=`, `>=`, `!=` and `=~` are operators and are never
     * interned through here as attrsets. */
    if (length > 1 && name[length - 1] == '=') {
        switch (name[length - 2]) {
            case '=': case '<': case '>': case '!': case '~':
                break;
            default:
                return PM_YID_ATTRSET;
        }
    }

    /* Constants start with an uppercase letter. Everything else the lexer hands
     * us that is not one of the sigils above is a local. */
    if (encoding->isupper_char(name, (ptrdiff_t) length)) return PM_YID_CONST;

    return PM_YID_LOCAL;
}

pm_yid_t
pm_yid_intern(pm_arena_t *arena, pm_constant_pool_t *pool, const uint8_t *name, size_t length, const pm_encoding_t *encoding) {
    /* The pool stores pointers, not copies, and interned names have to outlive
     * whatever scratch buffer they arrive in (usually the lexer's tokenbuf).
     * Names already in the pool are found without copying; new ones move into
     * the arena first. */
    pm_constant_id_t constant_id = pm_constant_pool_find(pool, name, length);

    if (constant_id == PM_CONSTANT_ID_UNSET) {
        uint8_t *stable = (uint8_t *) pm_arena_alloc(arena, length, 1);
        memcpy(stable, name, length);
        constant_id = pm_constant_pool_insert_constant(arena, pool, stable, length);
    }

    if (constant_id == PM_CONSTANT_ID_UNSET) return PM_YID_NULL;

    pm_yid_t serial = (pm_yid_t) constant_id + PM_YID_DYNAMIC_SERIAL_BASE;
    return (serial << PM_YID_SCOPE_SHIFT) | (pm_yid_t) pm_yid_type_for(name, length, encoding) | PM_YID_STATIC_SYM;
}

pm_constant_id_t
pm_yid_to_constant(pm_arena_t *arena, pm_constant_pool_t *pool, pm_yid_t id) {
    if (id == PM_YID_NULL) return PM_CONSTANT_ID_UNSET;

    if (!pm_yid_is_notop(id)) {
        const char *name = pm_yid_op_name(id);
        if (name == NULL) return PM_CONSTANT_ID_UNSET;
        return pm_constant_pool_insert_constant(arena, pool, (const uint8_t *) name, strlen(name));
    }

    pm_yid_t serial = id >> PM_YID_SCOPE_SHIFT;
    if (serial < PM_YID_DYNAMIC_SERIAL_BASE) return PM_CONSTANT_ID_UNSET;

    return (pm_constant_id_t) (serial - PM_YID_DYNAMIC_SERIAL_BASE);
}

pm_yid_t
pm_yid_attrset(pm_arena_t *arena, pm_constant_pool_t *pool, pm_yid_t id) {
    if (pm_yid_is_attrset(id)) return id;

    /* `[]` has a dedicated attrset ID rather than a name with `=` appended. */
    if (id == 145 /* RUBY_TOKEN_AREF */) return 146 /* RUBY_TOKEN_ASET */;

    pm_constant_id_t constant_id = pm_yid_to_constant(arena, pool, id);
    if (constant_id == PM_CONSTANT_ID_UNSET) return PM_YID_NULL;

    pm_constant_t *constant = pm_constant_pool_id_to_constant(pool, constant_id);

    /* Build the writer's name by appending `=`, then intern that. The result
     * has to carry ID_ATTRSET rather than whatever the name would classify as
     * on its own, so it is assembled here rather than through pm_yid_intern. */
    size_t length = constant->length + 1;
    uint8_t *name = (uint8_t *) pm_arena_alloc(arena, length, 1);
    memcpy(name, constant->start, constant->length);
    name[constant->length] = '=';

    pm_constant_id_t attrset_id = pm_constant_pool_insert_constant(arena, pool, name, length);
    if (attrset_id == PM_CONSTANT_ID_UNSET) return PM_YID_NULL;

    pm_yid_t serial = (pm_yid_t) attrset_id + PM_YID_DYNAMIC_SERIAL_BASE;
    return (serial << PM_YID_SCOPE_SHIFT) | PM_YID_ATTRSET | PM_YID_STATIC_SYM;
}
