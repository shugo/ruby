#ifndef PRISM_INTERNAL_PARSEY_H
#define PRISM_INTERNAL_PARSEY_H

#include "prism/internal/parser.h"

/*
 * Parse the Ruby source associated with the given parser using the parser
 * generated from the forked CRuby grammar (src/parsey/parse.y) and return the
 * tree.
 *
 * This is the entry point for the PM_OPTIONS_BACKEND_PARSE_Y backend. It
 * mirrors pm_parse() in that it always returns a tree (a pm_program_node_t),
 * even when the source could not be parsed. In that case the reasons are
 * appended to parser->error_list.
 *
 * Everything reachable from the returned tree is allocated out of the arenas
 * owned by the given parser, so the caller frees it exactly as it would free
 * the result of pm_parse().
 */
pm_node_t * pm_yparse(pm_parser_t *parser);

#endif
