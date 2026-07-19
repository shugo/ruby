/*
 * Tests for the ID shim that the parse.y backend's grammar uses in place of
 * CRuby's IDs (src/parsey/yid.h).
 *
 * These are C rather than Ruby because nothing in the shim is reachable from
 * the Ruby API: it sits between the forked grammar and prism's constant pool.
 * Once the grammar is ported far enough to build nodes, the differential tests
 * against the hand-written parser will cover it from the outside as well, but
 * the bit layout is fiddly enough to be worth pinning down directly.
 *
 * Run with `make test-parsey`.
 */

#include "yid.h"

#include "prism/internal/arena.h"
#include "prism/internal/encoding.h"

#include <stdio.h>
#include <string.h>

static pm_arena_t arena = { 0 };
static pm_constant_pool_t pool;
static int failures = 0;

static void
ok(int condition, const char *description) {
    if (!condition) {
        failures++;
        printf("not ok - %s\n", description);
    } else {
        printf("ok - %s\n", description);
    }
}

static pm_yid_t
intern(const char *name) {
    return pm_yid_intern(&arena, &pool, (const uint8_t *) name, strlen(name), PM_ENCODING_UTF_8_ENTRY);
}

/*
 * Whether the name the given ID resolves to through the constant pool is the
 * one we expect. This is the round trip that node creation depends on.
 */
static int
resolves_to(pm_yid_t id, const char *expected) {
    pm_constant_id_t constant_id = pm_yid_to_constant(&arena, &pool, id);
    if (constant_id == PM_CONSTANT_ID_UNSET) return 0;

    pm_constant_t *constant = pm_constant_pool_id_to_constant(&pool, constant_id);
    return constant->length == strlen(expected) && memcmp(constant->start, expected, constant->length) == 0;
}

/*
 * Every name the lexer hands the grammar has to classify the way CRuby's
 * rb_intern would, since the ported code branches on the type bits.
 */
static void
test_name_types(void) {
    struct { const char *name; int type; } names[] = {
        { "x",   PM_YID_LOCAL },
        { "foo", PM_YID_LOCAL },
        { "_1",  PM_YID_LOCAL },
        { "it",  PM_YID_LOCAL },
        { "Foo", PM_YID_CONST },
        { "@x",  PM_YID_INSTANCE },
        { "@@x", PM_YID_CLASS },
        { "$x",  PM_YID_GLOBAL },
        { "x=",  PM_YID_ATTRSET }
    };

    for (size_t index = 0; index < sizeof(names) / sizeof(names[0]); index++) {
        pm_yid_t id = intern(names[index].name);
        char description[64];

        snprintf(description, sizeof(description), "%s has the right type", names[index].name);
        ok(pm_yid_type(id) == names[index].type, description);

        snprintf(description, sizeof(description), "%s is not an operator", names[index].name);
        ok(pm_yid_is_notop(id), description);

        snprintf(description, sizeof(description), "%s round trips through the pool", names[index].name);
        ok(resolves_to(id, names[index].name), description);
    }
}

/*
 * Operator IDs are token values, not encoded names, so they sit below the
 * operator ceiling and get their names from a table instead of the pool.
 */
static void
test_operators(void) {
    struct { pm_yid_t id; const char *name; } operators[] = {
        { '+', "+" },
        { '-', "-" },
        { '<', "<" },
        { 134, "**" },
        { 135, "<=>" },
        { 140, "==" },
        { 145, "[]" },
        { 146, "[]=" }
    };

    for (size_t index = 0; index < sizeof(operators) / sizeof(operators[0]); index++) {
        pm_yid_t id = operators[index].id;
        const char *name = pm_yid_op_name(id);
        char description[64];

        snprintf(description, sizeof(description), "operator %s is named", operators[index].name);
        ok(name != NULL && strcmp(name, operators[index].name) == 0, description);

        snprintf(description, sizeof(description), "operator %s is an operator", operators[index].name);
        ok(!pm_yid_is_notop(id), description);

        snprintf(description, sizeof(description), "operator %s interns on demand", operators[index].name);
        ok(resolves_to(id, operators[index].name), description);
    }
}

static void
test_attrset(void) {
    pm_yid_t writer = pm_yid_attrset(&arena, &pool, intern("x"));
    ok(resolves_to(writer, "x="), "attrset of x is x=");
    ok(pm_yid_is_attrset(writer), "attrset of x is typed as a writer");

    /* `[]` is the one case where the writer is a different operator rather than
     * the name with `=` appended. */
    ok(pm_yid_attrset(&arena, &pool, 145) == 146, "attrset of [] is []=");

    ok(pm_yid_attrset(&arena, &pool, writer) == writer, "attrset of a writer is itself");
}

static void
test_identity(void) {
    ok(intern("foo") == intern("foo"), "the same name interns to the same id");
    ok(intern("foo") != intern("bar"), "different names intern to different ids");
    ok(intern("x") != intern("x="), "a name and its writer are different ids");

    /*
     * The dynamic serials are biased past the operator range specifically so
     * that the very first name interned is still classified as a name rather
     * than colliding with the operator IDs.
     */
    pm_arena_t fresh_arena = { 0 };
    pm_constant_pool_t fresh_pool;
    pm_constant_pool_init(&fresh_arena, &fresh_pool, 2);

    pm_yid_t first = pm_yid_intern(&fresh_arena, &fresh_pool, (const uint8_t *) "a", 1, PM_ENCODING_UTF_8_ENTRY);
    ok(pm_yid_is_notop(first), "the first name interned is not mistaken for an operator");

    pm_arena_cleanup(&fresh_arena);
}

int
main(void) {
    pm_constant_pool_init(&arena, &pool, 16);

    test_name_types();
    test_operators();
    test_attrset();
    test_identity();

    pm_arena_cleanup(&arena);

    if (failures > 0) {
        printf("\n%d failure(s)\n", failures);
        return 1;
    }

    printf("\nall assertions passed\n");
    return 0;
}
