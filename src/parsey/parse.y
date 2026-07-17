/**********************************************************************

  parse.y -

  This file is a fork of CRuby's parse.y, adapted to build prism's AST
  (pm_node_t) directly from the grammar actions rather than CRuby's NODE
  tree. It is the grammar behind the PM_OPTIONS_BACKEND_PARSE_Y backend.

  To keep future merges from upstream CRuby tractable, the structure of this
  file, the names of the grammar rules, and the names of the semantic helpers
  are deliberately kept aligned with CRuby's parse.y. Where a CRuby concept has
  a prism equivalent, the prism one is used:

    | CRuby            | here                                |
    | ---------------- | ----------------------------------- |
    | NODE             | pm_node_t                           |
    | ID / rb_intern   | pm_yid_t over pm_constant_pool      |
    | rb_parser_string | pm_ystring_t                        |
    | rb_encoding      | pm_encoding_t                       |
    | rb_ast_t arena   | pm_parser_t's arenas                |
    | YYLTYPE          | byte offsets into the source        |

  On locations. CRuby's lexer reads the source a line at a time through
  p->lex.gets, because it has to support streaming, and it tracks positions as
  (line, column) pairs. Prism has the whole source in memory and wants byte
  offsets. Rather than convert between the two, the line reader here hands the
  lexer slices of prism's own source buffer instead of copies of them, so that
  p->lex.pbeg, .pcur and .pend all point into the source and an offset is just
  `ptr - parser->start`. This is only sound because the lexer never writes
  through those pointers -- it accumulates into tokenbuf instead, and the one
  routine that does mutate a string in place, dedent_string, operates on the
  literals the lexer built rather than on the line buffer. Keep it that way:
  it is what makes the offsets exact by construction rather than by arithmetic
  that has to be kept in step with the lexer.

  The generated parser is compiled into libprism, which is loaded into CRuby
  processes that already export CRuby's own parser symbols, so every symbol
  defined here is either static or prefixed with pm_y.

**********************************************************************/

%{

/* The generated tables and yyparse() body trip several of the warnings that
 * prism builds with, and we do not want to relax them for the hand-written code
 * in this file. Everything lrama generates sits between this prologue and the
 * epilogue, so pushing the relaxed set here and popping it at the top of the
 * epilogue covers exactly the generated code, with no build-system change. */
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wconversion"
#pragma GCC diagnostic ignored "-Wsign-conversion"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#include "prism/internal/parsey.h"

#include "prism/internal/arena.h"
#include "prism/internal/constant_pool.h"
#include "prism/internal/parser.h"

#include "prism/ast.h"

#include <stdlib.h>
#include <string.h>

/* The state threaded through the parser. This is the fork of CRuby's
 * `struct parser_params`. For now it holds only what the placeholder grammar
 * needs; it grows into the full lexer state as the grammar is ported. */
struct pm_yparser {
    /* The prism parser that owns the arenas, the constant pool, the diagnostic
     * lists and the source we are parsing. Everything we allocate that is
     * reachable from the resulting tree comes from here. */
    pm_parser_t *pm;

    /* The root of the tree that the grammar built, set by the start rule. */
    pm_node_t *result;
};

/* Keep the generated entry point out of the global namespace: libprism is
 * loaded into processes that already have a yyparse from CRuby's own parser. */
#define yyparse pm_yyparse

/* The parser generator emits this prologue ahead of the token enum and the
 * YYSTYPE union, so pull in the header it generates alongside parse.c to get
 * them declared here. The generated parser includes it again, and the include
 * guard makes that a no-op. CRuby's parse.y includes its own generated parse.h
 * the same way and for the same reason. This resolves to src/parsey/parse.h:
 * a quoted include searches the including file's directory first. */
#include "parse.h"

static int yylex(YYSTYPE *lval, YYLTYPE *lloc, struct pm_yparser *yp);
static void yyerror(YYLTYPE *lloc, struct pm_yparser *yp, const char *msg);

%}

%expect 0
%define api.pure
%define parse.error verbose
%locations

%lex-param {struct pm_yparser *yp}
%parse-param {struct pm_yparser *yp}

/* Operator tokens are declared the way CRuby declares them, with their numbers
 * coming from defs/id.def by way of tool/id2token.rb rather than being written
 * out here. Two tokens are declared while the grammar is a placeholder so that
 * the build exercises the filter rather than assuming it works; the rest arrive
 * with the grammar. yid.c mirrors these numbers for the operator names, so they
 * have to agree with id.def.
 *
 * The keyword token is not incidental: lrama omits the trailing comma after
 * whichever token is numbered yymaxutok, on the assumption that it is the last
 * one declared (lib/lrama/output.rb, token_enums). Operator tokens are numbered
 * below the 258 that bison starts users at, so a grammar whose only tokens are
 * operators generates an enum that does not compile. CRuby never trips this
 * because its keywords sit above its operators; keep at least one token here
 * that does the same. */
%token tUPLUS       RUBY_TOKEN(UPLUS)  "unary+"
%token keyword_nil  258                "'nil'"

%union {
    pm_node_t *node;
}

%type <node> program

%%
program : /* none */
            {
                yp->result = NULL;
            }
        ;
%%

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic pop
#endif

/* The lexer. Ported from CRuby's parse.y in a later phase; for now the grammar
 * is empty so we only ever report end-of-input. */
static int
yylex(YYSTYPE *lval, YYLTYPE *lloc, struct pm_yparser *yp) {
    (void) lval;
    (void) lloc;
    (void) yp;
    return 0;
}

/* Report a syntax error against the source being parsed. */
static void
yyerror(YYLTYPE *lloc, struct pm_yparser *yp, const char *msg) {
    (void) lloc;
    (void) yp;
    (void) msg;
}

/**
 * Build the ProgramNode that wraps the statements the grammar produced. Mirrors
 * the tail of parse_program() in src/prism.c: an empty parse still yields a
 * ProgramNode with an empty StatementsNode so that consumers can rely on the
 * shape of the tree regardless of whether the parse succeeded.
 */
static pm_node_t *
pm_yparse_program(struct pm_yparser *yp, pm_node_t *statements) {
    pm_parser_t *parser = yp->pm;

    pm_statements_node_t *body;
    if (statements == NULL) {
        body = pm_statements_node_new(parser->arena, ++parser->node_id, 0, (pm_location_t) { 0 }, (pm_node_list_t) { 0 });
    } else {
        body = (pm_statements_node_t *) statements;
    }

    pm_constant_id_list_t locals = { 0 };
    return (pm_node_t *) pm_program_node_new(parser->arena, ++parser->node_id, 0, body->base.location, locals, body);
}

/**
 * Parse the Ruby source associated with the given parser with the forked CRuby
 * grammar and return the tree.
 */
pm_node_t *
pm_yparse(pm_parser_t *parser) {
    struct pm_yparser yp = {
        .pm = parser,
        .result = NULL
    };

    pm_yyparse(&yp);
    return pm_yparse_program(&yp, yp.result);
}
