// Parses a small corpus of valid and broken sources with the parse.y backend
// and checks the basic contract: parsing never crashes, always yields a tree,
// and reports errors exactly for the broken inputs. Run under the sanitizers
// in CI, this doubles as the memory-safety gate for the backend.

#include "prism.h"
#include "prism/internal/parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;

static void
assert_that(bool condition, const char *message, const char *source) {
    if (condition) {
        printf("ok - %s: %s\n", message, source);
    } else {
        printf("not ok - %s: %s\n", message, source);
        failures++;
    }
}

static void
check(const char *source, bool valid) {
    pm_arena_t *arena = pm_arena_new();
    pm_options_t *options = pm_options_new();
    pm_options_backend_set(options, "parse_y", 7);

    pm_parser_t *parser = pm_parser_new(arena, (const uint8_t *) source, strlen(source), options);
    pm_node_t *node = pm_parse(parser);

    assert_that(node != NULL, "yields a tree", source);
    if (valid) {
        assert_that(parser->error_list.size == 0, "parses cleanly", source);
    } else {
        assert_that(parser->error_list.size > 0, "reports an error", source);
    }

    pm_parser_free(parser);
    pm_options_free(options);
    pm_arena_free(arena);
}

int
main(void) {
    static const char *valid[] = {
        "1 + 2",
        "def foo(a, b = 1, *c, d:, **e, &f); a + b; end",
        "x = [1, 2, 3].map { |i| i * 2 }",
        "\"str#{interp}\" + <<~HEREDOC\n  text\nHEREDOC",
        "class Foo < Bar; def baz = super; end",
        "case x; in [Integer => a, *rest]; a; in {k:}; k; end",
        "foo(*a, **b, &c); def f(...) = bar(...)",
        "# encoding: euc-jp\nx = /pattern/i =~ '\xa4\xa2'",
        "a, (b, *c), d = e; ->(x; y) { x rescue y }",
        "BEGIN { a }; END { b }; alias $x $y",
    };

    static const char *broken[] = {
        "x = 1\ny = @@@ !\nz = 3",
        "def f(\nx = 1",
        "class A\n  def m\n    x = 1\n",
        "foo(1, 2\nbar 3",
        "x = \"abc",
        "x = <<E\nabc",
        "a = [1, 2",
        "def f; case x; in [",
        "\"#{",
        "begin\n rescue",
        "->() {",
        "a.b.",
        "=begin\nabc",
    };

    for (size_t i = 0; i < sizeof(valid) / sizeof(*valid); i++) check(valid[i], true);
    for (size_t i = 0; i < sizeof(broken) / sizeof(*broken); i++) check(broken[i], false);

    if (failures == 0) {
        printf("all assertions passed\n");
        return EXIT_SUCCESS;
    }
    printf("%d assertions failed\n", failures);
    return EXIT_FAILURE;
}
