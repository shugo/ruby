#ifndef PRISM_PARSEY_YSTRING_H
#define PRISM_PARSEY_YSTRING_H

#include "prism/internal/arena.h"
#include "prism/internal/encoding.h"

#include <stdbool.h>
#include <stddef.h>

/*
 * The string type the forked grammar and lexer carry, in place of CRuby's
 * rb_parser_string_t. Same shape, same operations, same names, so that the
 * ported code reads the way it does upstream; the encoding is prism's, and
 * there is one addition, below.
 *
 * A string is one of two things:
 *
 *   - Owned. Its bytes are malloc'd, NUL-terminated, and may be appended to or
 *     truncated. Everything the lexer builds -- string literals, symbols, the
 *     contents of heredocs -- is owned. Freed with pm_ystring_free.
 *   - Shared. Its bytes are a slice of the source prism was handed. Nothing
 *     owns them, they are not NUL-terminated, and they must not be modified.
 *     The line the lexer is reading is shared, which is what makes a byte
 *     offset `ptr - parser->start` rather than something the lexer has to keep
 *     a running count of (see the header of parse.y).
 *
 * CRuby has no such distinction because it copies each line out of the source.
 * The `shared` flag is what keeps the difference from being a silent
 * correctness problem: pm_ystring_modify, which every mutation goes through,
 * asserts on it.
 */

/*
 * How the bytes of a string relate to its encoding. These are CRuby's
 * rb_parser_string_coderange_type and must not be renumbered.
 */
typedef enum {
    /* Not scanned yet. */
    PM_YSTRING_CODERANGE_UNKNOWN = 0,

    /* Every byte is 7-bit, so the string reads the same in any of prism's
     * encodings. */
    PM_YSTRING_CODERANGE_7BIT = 1,

    /* Not 7-bit, but every character is valid in the string's encoding. */
    PM_YSTRING_CODERANGE_VALID = 2,

    /* Some byte sequence is not a character in the string's encoding. */
    PM_YSTRING_CODERANGE_BROKEN = 3
} pm_ystring_coderange_t;

typedef struct pm_ystring {
    /* What the bytes are, relative to the encoding. Computed on demand and
     * cached; cleared whenever the bytes change. */
    pm_ystring_coderange_t coderange;

    /* The encoding the bytes are in. */
    const pm_encoding_t *enc;

    /* The length of the string, not counting the NUL that terminates an owned
     * one. */
    long len;

    /* The bytes. For an owned string this is malloc'd and has a NUL at [len].
     * For a shared string it points into the source and has neither. */
    char *ptr;

    /* Whether ptr is a slice of the source rather than this string's own
     * memory: do not free it, do not write through it. */
    bool shared;

    /* Whether something long-lived (a heredoc's saved opening line) points at
     * this struct: the line recycler must not reuse it. */
    bool pinned;
} pm_ystring_t;

/* The accessors the ported code uses, under CRuby's names. */
#define PM_YSTRING_PTR(str) ((str)->ptr)
#define PM_YSTRING_LEN(str) ((str)->len)
#define PM_YSTRING_END(str) (&(str)->ptr[(str)->len])

/*
 * Allocate an owned string of the given bytes. Passing NULL for ptr gives a
 * string of len zero bytes, which is how the lexer starts one it is about to
 * append to.
 */
pm_ystring_t * pm_ystring_new(const char *ptr, long len, const pm_encoding_t *enc);

/*
 * Allocate a string that shares the given bytes rather than copying them. The
 * bytes must outlive the string and must not be written to; in practice they
 * are always a slice of the source being parsed.
 *
 * The string itself is allocated out of the given arena rather than malloc'd,
 * because the lexer hands these to the heredoc machinery, which keeps them
 * across lines; letting the arena free them removes the bookkeeping CRuby needs
 * for the same lifetime (its lex.string_buffer).
 */
pm_ystring_t * pm_ystring_new_shared(pm_arena_t *arena, const char *ptr, long len, const pm_encoding_t *enc);

/* Free an owned string. A shared one is a no-op: the arena owns it. */
void pm_ystring_free(pm_ystring_t *str);

/* A deep copy of the given string, always owned. */
pm_ystring_t * pm_ystring_deep_copy(const pm_ystring_t *orig);

/*
 * Declare that the bytes of the string are about to change: drops the cached
 * coderange, and asserts that the string is not a shared one.
 */
void pm_ystring_modify(pm_ystring_t *str);

/* Set the encoding of the string without reinterpreting its bytes. */
void pm_ystring_set_encoding(pm_ystring_t *str, const pm_encoding_t *enc);

/*
 * Set the encoding of the string, dropping the cached coderange unless the
 * string is 7-bit, in which case it reads the same in any encoding.
 */
pm_ystring_t * pm_ystring_associate_encoding(pm_ystring_t *str, const pm_encoding_t *enc);

/* The coderange of the string, scanning it if it has not been scanned. */
pm_ystring_coderange_t pm_ystring_coderange(pm_ystring_t *str);

/* Whether every byte of the string is 7-bit. */
bool pm_ystring_ascii_only_p(pm_ystring_t *str);

/* The coderange of the given bytes read in the given encoding. */
pm_ystring_coderange_t pm_ystring_coderange_scan(const char *ptr, long len, const pm_encoding_t *enc);

/*
 * An encoding that both strings can be read in, or NULL if there is none.
 * Mirrors CRuby's rb_parser_enc_compatible.
 */
const pm_encoding_t * pm_ystring_compatible_encoding(pm_ystring_t *str1, pm_ystring_t *str2);

/* Truncate or extend the string to the given length, which must not exceed the
 * bytes it already has. */
void pm_ystring_set_len(pm_ystring_t *str, long len);

/* Append the given bytes to the string. */
void pm_ystring_cat(pm_ystring_t *str, const char *ptr, long len);

/* Append the given string to the string. */
void pm_ystring_append(pm_ystring_t *str, pm_ystring_t *str2);

/* Reallocate the string to the given length, zero-filling any growth. */
void pm_ystring_resize(pm_ystring_t *str, long len);

/* Whether the two strings have the same bytes. Encoding is not considered,
 * matching CRuby's rb_parser_string_hash_cmp. */
bool pm_ystring_equal(const pm_ystring_t *str1, const pm_ystring_t *str2);

/* A hash of the string's bytes, for the tables the parser keys by name. */
size_t pm_ystring_hash(const pm_ystring_t *str);

#endif
