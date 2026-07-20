/*
 * Tests for the string type the parse.y backend's grammar carries in place of
 * CRuby's rb_parser_string_t (src/parsey/ystring.h).
 *
 * As with yid_test, these are C because the type sits below anything the Ruby
 * API can reach. Run with `make test-parsey`.
 */

#include "ystring.h"

#include "prism/internal/arena.h"
#include "prism/internal/encoding.h"

#include <stdio.h>
#include <string.h>

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

static int
has_bytes(const pm_ystring_t *str, const char *expected) {
    return str->len == (long) strlen(expected) && memcmp(str->ptr, expected, (size_t) str->len) == 0;
}

static void
test_owned(void) {
    pm_ystring_t *str = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);

    ok(has_bytes(str, "hello"), "an owned string holds the bytes it was given");
    ok(!str->shared, "an owned string is not shared");
    ok(str->ptr[str->len] == '\0', "an owned string is NUL terminated");
    ok(str->enc == PM_ENCODING_UTF_8_ENTRY, "an owned string keeps its encoding");

    /* The bytes are copied, not borrowed: the source can go away. */
    char source[] = "world";
    pm_ystring_t *copied = pm_ystring_new(source, 5, PM_ENCODING_UTF_8_ENTRY);
    memset(source, 'x', 5);
    ok(has_bytes(copied, "world"), "an owned string copies the bytes it was given");

    pm_ystring_free(str);
    pm_ystring_free(copied);

    /* An empty string is what the lexer starts with before appending. */
    pm_ystring_t *empty = pm_ystring_new(NULL, 0, PM_ENCODING_UTF_8_ENTRY);
    ok(empty->len == 0, "a string can start empty");
    ok(empty->ptr[0] == '\0', "an empty string is still NUL terminated");
    pm_ystring_free(empty);
}

static void
test_shared(void) {
    pm_arena_t arena = { 0 };
    const char *source = "foo = 1\nbar = 2\n";

    /* This is the shape the line reader produces: a slice of the source, with
     * its newline, borrowed rather than copied. */
    pm_ystring_t *line = pm_ystring_new_shared(&arena, source, 8, PM_ENCODING_UTF_8_ENTRY);

    ok(line->shared, "a shared string is marked shared");
    ok(line->ptr == source, "a shared string points at the source rather than a copy");
    ok(has_bytes(line, "foo = 1\n"), "a shared string reads the slice it was given");

    /* The whole point: an offset into the source is a subtraction, with no
     * bookkeeping to get out of step with the lexer. */
    pm_ystring_t *second = pm_ystring_new_shared(&arena, source + 8, 8, PM_ENCODING_UTF_8_ENTRY);
    ok(second->ptr - source == 8, "a shared string's offset into the source is its pointer difference");
    ok(has_bytes(second, "bar = 2\n"), "the second line reads correctly");

    /* Freeing a shared string must not free the source. The arena owns the
     * struct, so this is a no-op rather than a double free. */
    pm_ystring_free(line);
    ok(strcmp(source, "foo = 1\nbar = 2\n") == 0, "freeing a shared string leaves the source alone");

    pm_arena_cleanup(&arena);
}

static void
test_coderange(void) {
    pm_ystring_t *ascii = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);
    ok(pm_ystring_coderange(ascii) == PM_YSTRING_CODERANGE_7BIT, "an ASCII string scans as 7bit");
    ok(pm_ystring_ascii_only_p(ascii), "an ASCII string is ascii only");

    /* "日本語" in UTF-8. */
    pm_ystring_t *utf8 = pm_ystring_new("\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e", 9, PM_ENCODING_UTF_8_ENTRY);
    ok(pm_ystring_coderange(utf8) == PM_YSTRING_CODERANGE_VALID, "a multibyte UTF-8 string scans as valid");
    ok(!pm_ystring_ascii_only_p(utf8), "a multibyte string is not ascii only");

    /* A truncated multibyte sequence is not a character in UTF-8. */
    pm_ystring_t *broken = pm_ystring_new("\xe6\x97", 2, PM_ENCODING_UTF_8_ENTRY);
    ok(pm_ystring_coderange(broken) == PM_YSTRING_CODERANGE_BROKEN, "a truncated UTF-8 sequence scans as broken");

    /* The same bytes are never broken in ASCII-8BIT, where every byte is a
     * character. */
    pm_ystring_t *binary = pm_ystring_new("\xe6\x97", 2, PM_ENCODING_ASCII_8BIT_ENTRY);
    ok(pm_ystring_coderange(binary) == PM_YSTRING_CODERANGE_VALID, "high bytes are valid in ASCII-8BIT");

    /* The scan is cached, and dropped when the bytes change. */
    ok(ascii->coderange == PM_YSTRING_CODERANGE_7BIT, "the coderange is cached after scanning");
    pm_ystring_cat(ascii, "\xe6\x97\xa5", 3);
    ok(ascii->coderange == PM_YSTRING_CODERANGE_UNKNOWN, "appending drops the cached coderange");
    ok(pm_ystring_coderange(ascii) == PM_YSTRING_CODERANGE_VALID, "the coderange is rescanned after appending");

    pm_ystring_free(ascii);
    pm_ystring_free(utf8);
    pm_ystring_free(broken);
    pm_ystring_free(binary);
}

static void
test_associate_encoding(void) {
    /* Reinterpreting a 7-bit string is free: it reads the same either way, so
     * the scan it already paid for still holds. */
    pm_ystring_t *ascii = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_coderange(ascii);
    pm_ystring_associate_encoding(ascii, PM_ENCODING_ASCII_8BIT_ENTRY);
    ok(ascii->enc == PM_ENCODING_ASCII_8BIT_ENTRY, "associating sets the encoding");
    ok(ascii->coderange == PM_YSTRING_CODERANGE_7BIT, "associating keeps a 7bit string's coderange");

    /* Reinterpreting anything else means the bytes have to be read again. */
    pm_ystring_t *utf8 = pm_ystring_new("\xe6\x97\xa5", 3, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_coderange(utf8);
    pm_ystring_associate_encoding(utf8, PM_ENCODING_ASCII_8BIT_ENTRY);
    ok(utf8->coderange == PM_YSTRING_CODERANGE_UNKNOWN, "associating drops a multibyte string's coderange");

    pm_ystring_free(ascii);
    pm_ystring_free(utf8);
}

static void
test_compatible_encoding(void) {
    pm_ystring_t *ascii = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *ascii2 = pm_ystring_new("world", 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *utf8 = pm_ystring_new("\xe6\x97\xa5", 3, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *binary = pm_ystring_new("\xff\xfe", 2, PM_ENCODING_ASCII_8BIT_ENTRY);
    pm_ystring_t *empty = pm_ystring_new(NULL, 0, PM_ENCODING_ASCII_8BIT_ENTRY);

    ok(pm_ystring_compatible_encoding(ascii, ascii2) == PM_ENCODING_UTF_8_ENTRY, "same encoding is compatible with itself");
    ok(pm_ystring_compatible_encoding(utf8, empty) == PM_ENCODING_UTF_8_ENTRY, "an empty string takes the other's encoding");

    /* A 7-bit string reads as anything, so it yields to the other. */
    pm_ystring_t *ascii_binary = pm_ystring_new("hello", 5, PM_ENCODING_ASCII_8BIT_ENTRY);
    ok(pm_ystring_compatible_encoding(ascii_binary, utf8) == PM_ENCODING_UTF_8_ENTRY, "a 7bit string yields to a multibyte one");
    ok(pm_ystring_compatible_encoding(utf8, ascii_binary) == PM_ENCODING_UTF_8_ENTRY, "a multibyte string wins over a 7bit one");

    /* Two strings that each have bytes only meaningful in their own encoding
     * cannot both be read. */
    ok(pm_ystring_compatible_encoding(utf8, binary) == NULL, "two non-7bit strings in different encodings are incompatible");

    pm_ystring_free(ascii);
    pm_ystring_free(ascii2);
    pm_ystring_free(utf8);
    pm_ystring_free(binary);
    pm_ystring_free(empty);
    pm_ystring_free(ascii_binary);
}

static void
test_cat(void) {
    pm_ystring_t *str = pm_ystring_new("foo", 3, PM_ENCODING_UTF_8_ENTRY);

    pm_ystring_cat(str, "bar", 3);
    ok(has_bytes(str, "foobar"), "appending extends the string");
    ok(str->ptr[str->len] == '\0', "the string is still NUL terminated after appending");

    pm_ystring_cat(str, "", 0);
    ok(has_bytes(str, "foobar"), "appending nothing changes nothing");

    /* Appending a string to itself: the realloc can move the buffer, taking
     * the bytes being read out from under the copy. */
    pm_ystring_cat(str, str->ptr, str->len);
    ok(has_bytes(str, "foobarfoobar"), "a string can be appended to itself");

    /* The same, from the middle of its own buffer. */
    pm_ystring_t *self = pm_ystring_new("abcdef", 6, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_cat(self, self->ptr + 3, 3);
    ok(has_bytes(self, "abcdefdef"), "a string can be appended to from inside itself");

    pm_ystring_t *other = pm_ystring_new("!", 1, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_append(self, other);
    ok(has_bytes(self, "abcdefdef!"), "one string can be appended to another");

    pm_ystring_free(str);
    pm_ystring_free(self);
    pm_ystring_free(other);
}

static void
test_resize_and_set_len(void) {
    pm_ystring_t *str = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);

    pm_ystring_set_len(str, 3);
    ok(has_bytes(str, "hel"), "setting a shorter length truncates");
    ok(str->ptr[str->len] == '\0', "the string is NUL terminated after truncating");

    pm_ystring_resize(str, 6);
    ok(str->len == 6, "resizing longer sets the length");
    ok(memcmp(str->ptr, "hel\0\0\0", 6) == 0, "resizing longer zero fills");

    pm_ystring_resize(str, 2);
    ok(has_bytes(str, "he"), "resizing shorter truncates");

    /* Truncating a 7-bit string leaves it 7-bit; truncating a multibyte one can
     * cut a character in half, so it has to be scanned again. */
    pm_ystring_t *utf8 = pm_ystring_new("\xe6\x97\xa5\xe6\x9c\xac", 6, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_coderange(utf8);
    pm_ystring_set_len(utf8, 4);
    ok(utf8->coderange == PM_YSTRING_CODERANGE_UNKNOWN, "truncating a multibyte string drops its coderange");
    ok(pm_ystring_coderange(utf8) == PM_YSTRING_CODERANGE_BROKEN, "truncating mid character leaves it broken");

    pm_ystring_free(str);
    pm_ystring_free(utf8);
}

static void
test_equal_and_hash(void) {
    pm_ystring_t *a = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *b = pm_ystring_new("hello", 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *c = pm_ystring_new("world", 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *d = pm_ystring_new("hell", 4, PM_ENCODING_UTF_8_ENTRY);

    ok(pm_ystring_equal(a, b), "strings with the same bytes are equal");
    ok(!pm_ystring_equal(a, c), "strings with different bytes are not equal");
    ok(!pm_ystring_equal(a, d), "strings with different lengths are not equal");

    ok(pm_ystring_hash(a) == pm_ystring_hash(b), "equal strings hash the same");
    ok(pm_ystring_hash(a) != pm_ystring_hash(c), "different strings hash differently");

    /* A shared string and an owned one with the same bytes are the same string
     * as far as the tables the parser keys by name are concerned. */
    pm_arena_t arena = { 0 };
    pm_ystring_t *shared = pm_ystring_new_shared(&arena, "hello", 5, PM_ENCODING_UTF_8_ENTRY);
    ok(pm_ystring_equal(a, shared), "a shared string equals an owned one with the same bytes");
    ok(pm_ystring_hash(a) == pm_ystring_hash(shared), "a shared string hashes like an owned one");
    pm_arena_cleanup(&arena);

    pm_ystring_free(a);
    pm_ystring_free(b);
    pm_ystring_free(c);
    pm_ystring_free(d);
}

static void
test_deep_copy(void) {
    pm_arena_t arena = { 0 };
    char source[] = "hello";

    /* Copying a shared string is how the lexer takes ownership of bytes it
     * wants to keep past the line they came from. */
    pm_ystring_t *shared = pm_ystring_new_shared(&arena, source, 5, PM_ENCODING_UTF_8_ENTRY);
    pm_ystring_t *copy = pm_ystring_deep_copy(shared);

    ok(!copy->shared, "a copy of a shared string is owned");
    ok(copy->ptr != shared->ptr, "a copy of a shared string has its own bytes");
    ok(has_bytes(copy, "hello"), "a copy has the same bytes");

    memset(source, 'x', 5);
    ok(has_bytes(copy, "hello"), "a copy survives its source changing");

    pm_ystring_free(copy);
    pm_arena_cleanup(&arena);
}

int
main(void) {
    test_owned();
    test_shared();
    test_coderange();
    test_associate_encoding();
    test_compatible_encoding();
    test_cat();
    test_resize_and_set_len();
    test_equal_and_hash();
    test_deep_copy();

    if (failures > 0) {
        printf("\n%d failure(s)\n", failures);
        return 1;
    }

    printf("\nall assertions passed\n");
    return 0;
}
