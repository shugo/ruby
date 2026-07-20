#ifndef PRISM_PARSEY_YENC_H
#define PRISM_PARSEY_YENC_H

#include "prism/internal/encoding.h"

/*
 * The encoding calls the forked grammar and lexer make, expressed in terms of
 * prism's encoding tables.
 *
 * CRuby's parser talks to Onigmo, whose interface reports the width of the next
 * character through a packed integer that has to be unpacked with
 * MBCLEN_CHARFOUND_P and MBCLEN_CHARFOUND_LEN. Prism's pm_encoding_t answers
 * the same question with a width that is simply 0 when the character is not
 * valid, so the two macros collapse to a comparison and an identity. They are
 * kept under their CRuby names anyway: the ported code reads the way it does
 * upstream, and the shape of the call sites (scan, test, advance) survives.
 *
 * Prism's encodings are all ASCII-compatible, and the parser only ever sets an
 * encoding that pm_encoding_find returned, so the asciicompat checks CRuby
 * makes have no counterpart here.
 */

/* The width of the next character, or 0 if it is not valid in the encoding. */
static inline int
pm_yenc_precise_mbclen(const char *ptr, const char *end, const pm_encoding_t *enc) {
    if (ptr >= end) return 0;
    /* every encoding prism supports is ASCII-compatible, so the common case
     * never needs the table lookup */
    if ((unsigned char) *ptr < 0x80) return 1;
    return (int) enc->char_width((const uint8_t *) ptr, (ptrdiff_t) (end - ptr));
}

#define rb_enc_precise_mbclen(ptr, end, enc) pm_yenc_precise_mbclen((ptr), (end), (enc))

/* Whether the width reported by rb_enc_precise_mbclen found a character. */
#define MBCLEN_CHARFOUND_P(ret) ((ret) > 0)

/* The width of the character that rb_enc_precise_mbclen found. */
#define MBCLEN_CHARFOUND_LEN(ret) (ret)

#endif
