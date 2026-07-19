#include "ystring.h"
#include "yenc.h"

#include "prism/compiler/align.h"

#include "prism/internal/allocator.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* An owned string always has a NUL after its bytes, so that the ported lexer
 * can keep using the C string calls it uses upstream. */
#define PM_YSTRING_TERM_LEN 1
#define PM_YSTRING_TERM_FILL(str) ((str)->ptr[(str)->len] = '\0')

pm_ystring_t *
pm_ystring_new(const char *ptr, long len, const pm_encoding_t *enc) {
    assert(len >= 0);

    pm_ystring_t *str = xcalloc(1, sizeof(pm_ystring_t));
    if (str == NULL) abort();

    str->ptr = xcalloc((size_t) len + PM_YSTRING_TERM_LEN, sizeof(char));
    if (str->ptr == NULL) abort();

    if (ptr != NULL) memcpy(str->ptr, ptr, (size_t) len);

    str->len = len;
    str->enc = enc;
    str->coderange = PM_YSTRING_CODERANGE_UNKNOWN;
    str->shared = false;
    str->pinned = false;
    PM_YSTRING_TERM_FILL(str);

    return str;
}

pm_ystring_t *
pm_ystring_new_shared(pm_arena_t *arena, const char *ptr, long len, const pm_encoding_t *enc) {
    assert(len >= 0);

    pm_ystring_t *str = (pm_ystring_t *) pm_arena_alloc(arena, sizeof(pm_ystring_t), PRISM_ALIGNOF(pm_ystring_t));

    /* The cast drops const from bytes we have promised not to write to. The
     * shared flag is what enforces that promise, in pm_ystring_modify. */
    str->ptr = (char *) (uintptr_t) ptr;
    str->len = len;
    str->enc = enc;
    str->coderange = PM_YSTRING_CODERANGE_UNKNOWN;
    str->shared = true;
    str->pinned = false;

    return str;
}

void
pm_ystring_free(pm_ystring_t *str) {
    if (str == NULL) return;

    /* A shared string owns neither its bytes nor itself. */
    if (str->shared) return;

    xfree(str->ptr);
    xfree_sized(str, sizeof(pm_ystring_t));
}

pm_ystring_t *
pm_ystring_deep_copy(const pm_ystring_t *orig) {
    pm_ystring_t *str = pm_ystring_new(orig->ptr, orig->len, orig->enc);
    str->coderange = orig->coderange;
    return str;
}

void
pm_ystring_modify(pm_ystring_t *str) {
    /* Shared bytes belong to the source. Anything that reaches here with one
     * is a porting mistake, and a silent one if it is not caught: it would
     * corrupt the source out from under the offsets that point into it. */
    assert(!str->shared);

    str->coderange = PM_YSTRING_CODERANGE_UNKNOWN;
}

void
pm_ystring_set_encoding(pm_ystring_t *str, const pm_encoding_t *enc) {
    str->enc = enc;
}

pm_ystring_t *
pm_ystring_associate_encoding(pm_ystring_t *str, const pm_encoding_t *enc) {
    if (str->enc == enc) return str;

    /* A 7-bit string reads the same in every encoding prism supports, so the
     * scan it already paid for still holds. */
    if (!pm_ystring_ascii_only_p(str)) str->coderange = PM_YSTRING_CODERANGE_UNKNOWN;

    pm_ystring_set_encoding(str, enc);
    return str;
}

/* The first byte at or after ptr with its high bit set, or NULL. */
static const char *
pm_ystring_search_nonascii(const char *ptr, const char *end) {
    for (const char *cursor = ptr; cursor < end; cursor++) {
        if (*cursor & 0x80) return cursor;
    }

    return NULL;
}

pm_ystring_coderange_t
pm_ystring_coderange_scan(const char *ptr, long len, const pm_encoding_t *enc) {
    const char *end = ptr + len;

    ptr = pm_ystring_search_nonascii(ptr, end);
    if (ptr == NULL) return PM_YSTRING_CODERANGE_7BIT;

    /* ASCII-8BIT gives every byte sequence a meaning, so it is never broken. */
    if (enc == PM_ENCODING_ASCII_8BIT_ENTRY) return PM_YSTRING_CODERANGE_VALID;

    for (;;) {
        int width = rb_enc_precise_mbclen(ptr, end, enc);
        if (!MBCLEN_CHARFOUND_P(width)) return PM_YSTRING_CODERANGE_BROKEN;

        ptr += MBCLEN_CHARFOUND_LEN(width);
        if (ptr == end) break;

        ptr = pm_ystring_search_nonascii(ptr, end);
        if (ptr == NULL) break;
    }

    return PM_YSTRING_CODERANGE_VALID;
}

pm_ystring_coderange_t
pm_ystring_coderange(pm_ystring_t *str) {
    if (str->coderange == PM_YSTRING_CODERANGE_UNKNOWN) {
        str->coderange = pm_ystring_coderange_scan(str->ptr, str->len, str->enc);
    }

    return str->coderange;
}

bool
pm_ystring_ascii_only_p(pm_ystring_t *str) {
    return pm_ystring_coderange(str) == PM_YSTRING_CODERANGE_7BIT;
}

const pm_encoding_t *
pm_ystring_compatible_encoding(pm_ystring_t *str1, pm_ystring_t *str2) {
    const pm_encoding_t *enc1 = str1->enc;
    const pm_encoding_t *enc2 = str2->enc;

    if (enc1 == NULL || enc2 == NULL) return NULL;
    if (enc1 == enc2) return enc1;

    /* An empty string constrains nothing, so the other one's encoding wins --
     * unless the other one is the empty one's and has bytes that only make
     * sense in its own encoding. */
    if (str2->len == 0) return enc1;
    if (str1->len == 0) return pm_ystring_ascii_only_p(str2) ? enc1 : enc2;

    pm_ystring_coderange_t cr1 = pm_ystring_coderange(str1);
    pm_ystring_coderange_t cr2 = pm_ystring_coderange(str2);

    /* A 7-bit string can be read as the other's encoding. If both are 7-bit
     * the encodings differ only in name here, and the first one is as good as
     * the second. If neither is, there is no encoding that reads both. */
    if (cr1 != cr2) {
        if (cr1 == PM_YSTRING_CODERANGE_7BIT) return enc2;
        if (cr2 == PM_YSTRING_CODERANGE_7BIT) return enc1;
    }

    if (cr2 == PM_YSTRING_CODERANGE_7BIT) return enc1;
    if (cr1 == PM_YSTRING_CODERANGE_7BIT) return enc2;

    return NULL;
}

void
pm_ystring_set_len(pm_ystring_t *str, long len) {
    assert(!str->shared);
    assert(len >= 0 && len <= str->len);

    /* Truncating a 7-bit string leaves it 7-bit. Truncating any other kind can
     * cut a character in half, so what it is has to be worked out again. */
    if (str->coderange != PM_YSTRING_CODERANGE_UNKNOWN && str->coderange != PM_YSTRING_CODERANGE_7BIT && len < str->len) {
        str->coderange = PM_YSTRING_CODERANGE_UNKNOWN;
    }

    str->len = len;
    PM_YSTRING_TERM_FILL(str);
}

void
pm_ystring_cat(pm_ystring_t *str, const char *ptr, long len) {
    pm_ystring_modify(str);
    if (len == 0) return;

    assert(len > 0);

    /* The bytes being appended may live inside this string's own buffer, which
     * the realloc below would move out from under them. Remember where they
     * are so they can be found again afterwards. */
    long off = -1;
    if (ptr >= str->ptr && ptr <= str->ptr + str->len) off = (long) (ptr - str->ptr);

    long total = str->len + len;
    char *reallocated = xrealloc_sized(str->ptr, (size_t) total + PM_YSTRING_TERM_LEN, (size_t) str->len + PM_YSTRING_TERM_LEN);
    if (reallocated == NULL) abort();
    str->ptr = reallocated;

    if (off != -1) ptr = str->ptr + off;

    memcpy(str->ptr + str->len, ptr, (size_t) len);
    str->len = total;
    PM_YSTRING_TERM_FILL(str);
}

void
pm_ystring_append(pm_ystring_t *str, pm_ystring_t *str2) {
    pm_ystring_cat(str, str2->ptr, str2->len);
}

void
pm_ystring_resize(pm_ystring_t *str, long len) {
    pm_ystring_modify(str);
    assert(len >= 0);

    long olen = str->len;
    if (len == olen) return;

    char *reallocated = xrealloc_sized(str->ptr, (size_t) len + PM_YSTRING_TERM_LEN, (size_t) olen + PM_YSTRING_TERM_LEN);
    if (reallocated == NULL) abort();
    str->ptr = reallocated;

    if (len > olen) memset(str->ptr + olen, 0, (size_t) (len - olen));

    str->len = len;
    PM_YSTRING_TERM_FILL(str);
}

bool
pm_ystring_equal(const pm_ystring_t *str1, const pm_ystring_t *str2) {
    if (str1->len != str2->len) return false;
    return memcmp(str1->ptr, str2->ptr, (size_t) str1->len) == 0;
}

size_t
pm_ystring_hash(const pm_ystring_t *str) {
    /* djb2, as CRuby's parser_memhash uses. */
    size_t hash = 5381;
    for (long index = 0; index < str->len; index++) {
        hash = ((hash << 5) + hash) + (size_t) (unsigned char) str->ptr[index];
    }

    return hash;
}
