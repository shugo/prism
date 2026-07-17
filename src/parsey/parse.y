/**********************************************************************

  parse.y -

  This file is a fork of CRuby's parse.y, adapted to build prism's AST
  (pm_node_t) directly from the grammar actions rather than CRuby's NODE
  tree. It is the grammar behind the PM_OPTIONS_BACKEND_PARSE_Y backend.

  To keep future merges from upstream CRuby tractable, the structure of this
  file, the names of the grammar rules, and the names of the semantic helpers
  are deliberately kept aligned with CRuby's parse.y. Where a CRuby concept has
  a prism equivalent, the prism one is used, and wherever possible the switch
  happens in the adapter layer at the top of this prologue rather than at the
  use sites, so that the body of the file stays diffable against upstream:

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
  `ptr - p->pm->start`. This is only sound because the lexer never writes
  through those pointers -- it accumulates into tokenbuf instead, and the one
  routine that does mutate a string in place, dedent_string, operates on the
  literals the lexer built rather than on the line buffer. It also means the
  line buffer is not NUL terminated the way CRuby's copied lines are, so
  nothing may run off the end of a line expecting a NUL to stop it; reads have
  to be bounded by lex.pend.

  The generated parser is compiled into libprism, which is loaded into CRuby
  processes that already export CRuby's own parser symbols, so every symbol
  defined here is either static or prefixed with pm_y.

**********************************************************************/

%{

/* The generated tables and yyparse() body trip several of the warnings that
 * prism builds with, and we do not want to relax them for the hand-written code
 * in this file. Everything lrama generates sits between this prologue and the
 * epilogue, and the grammar text this file keeps from CRuby's parse.y was
 * written against CRuby's warning set, so the relaxed set covers the whole
 * file. */
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic ignored "-Wconversion"
#pragma GCC diagnostic ignored "-Wsign-conversion"
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#pragma GCC diagnostic ignored "-Wunused-function"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
#endif

#include "prism/internal/parsey.h"

#include "prism/compiler/align.h"

#include "prism/internal/allocator.h"
#include "prism/internal/arena.h"
#include "prism/internal/constant_pool.h"
#include "prism/internal/diagnostic.h"
#include "prism/internal/encoding.h"
#include "prism/internal/integer.h"
#include "prism/internal/line_offset_list.h"
#include "prism/internal/node.h"
#include "prism/internal/parser.h"
#include "prism/internal/stringy.h"

#include "prism/ast.h"

#include "yenc.h"
#include "yid.h"
#include "ystring.h"

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * ADAPTERS. Everything in this section exists so that the code this file keeps
 * from CRuby's parse.y can keep its upstream spelling. Each CRuby name is
 * mapped onto the prism concept that replaces it; the mapping happens here,
 * once, instead of at thousands of use sites.
 */

/* The parser state. The struct itself is declared below under its CRuby name;
 * rb_parser_t is the alias the function signatures use. */
struct parser_params;
typedef struct parser_params rb_parser_t;

/* Names. See yid.h: same bit layout as CRuby's IDs, resolved through the
 * prism parser's constant pool instead of a global symbol table. */
typedef pm_yid_t ID;

/* Strings the parser builds or borrows. See ystring.h. */
typedef pm_ystring_t rb_parser_string_t;

/* Encodings. In universal-parser CRuby rb_encoding is already an opaque
 * pointer; here it is prism's encoding table entry. */
typedef const pm_encoding_t rb_encoding;

/* Nodes. Every node the fork builds is a prism node; the many rb_node_xxx_t
 * names all collapse onto pm_node_t for now and sharpen into specific prism
 * node or builder types as the actions that use them are ported. */
typedef pm_node_t NODE;

/* Locations. A byte-offset range in the source, in place of CRuby's
 * (line, column) pairs; see the header comment. YYLTYPE is declared before the
 * generated parse.h is included so that it wins. */
typedef struct {
    uint32_t beg;
    uint32_t end;
} pm_yloc_t;
#define YYLTYPE pm_yloc_t
#define YYLTYPE_IS_DECLARED 1
typedef pm_yloc_t rb_code_location_t;

/* CRuby positions survive only in a couple of corners (token_info); give them
 * the smallest type that keeps those corners compiling. */
typedef struct {
    int lineno;
    int column;
} rb_code_position_t;

/* The byte offset of a pointer into the source being parsed. Only valid for
 * pointers into the source, which is what lex.pbeg/.pcur/.pend are. */
#define YOFF(ptr) ((uint32_t) ((const uint8_t *) (ptr) - p->pm->start))

/* The byte-offset YYLTYPE as a prism location. */
static inline pm_location_t
pm_yloc(const pm_yloc_t *loc)
{
    return (pm_location_t) { loc->beg, loc->end - loc->beg };
}

/* The handful of places that still mention VALUE are all in code that is
 * stubbed out pending its port; the typedef keeps their signatures compiling
 * and nothing else. */
typedef intptr_t VALUE;
#define Qnil ((VALUE) 0)
#define Qfalse ((VALUE) 0)
#define Qtrue ((VALUE) 2)
#define NIL_P(v) ((v) == Qnil)
#define RTEST(v) ((v) != Qnil && (v) != Qfalse)

/* Memory. CRuby's parser allocates transient state with the x-family, which
 * prism also provides (prism/internal/allocator.h); the ALLOC macros are the
 * spellings parse.y uses. */
#define ALLOC(type) ((type *) xmalloc(sizeof(type)))
#define ALLOC_N(type, n) ((type *) xmalloc(sizeof(type) * (size_t) (n)))
#define ZALLOC(type) ((type *) xcalloc(1, sizeof(type)))
#define REALLOC_N(var, type, n) ((var) = (type *) xrealloc((void *) (var), sizeof(type) * (size_t) (n)))
#define MEMCPY(p1, p2, type, n) memcpy((p1), (p2), sizeof(type) * (size_t) (n))
#define MEMMOVE(p1, p2, type, n) memmove((p1), (p2), sizeof(type) * (size_t) (n))
#define ruby_sized_xfree(ptr, size) xfree_sized((ptr), (size))
#define SIZED_REALLOC_N(v, T, m, n) REALLOC_N(v, T, m)

/* Bit fields of enum type are an ABI headache CRuby works around per compiler;
 * the fork stores them as plain unsigned bits. */
#define BITFIELD(type, name, size) unsigned int name : size

/* rb_bug is for states that indicate a broken parser rather than broken input.
 * There is no CRuby runtime here to report into, so fail hard and loudly. */
#define rb_bug(...) (fprintf(stderr, "[prism parse.y bug] " __VA_ARGS__), fprintf(stderr, "\n"), abort())

#define RUBY_FUNC_EXPORTED static
#define RBIMPL_ATTR_NONNULL(list)
#define RBIMPL_ATTR_FORMAT(x, y, z)
#define RBIMPL_ATTR_PRINTF_FORMAT(y, z)
#define PRINTF_ARGS(decl, a, b) decl
#define ASSUME(expr) ((void) 0)
#define UNREACHABLE_RETURN(val) return (val)
#define RB_GC_GUARD(v) (v)
#define FLEX_ARY_LEN 1

#ifndef TRUE
#define TRUE 1
#endif
#ifndef FALSE
#define FALSE 0
#endif

#define rb_long2int(n) ((int) (n))
#define numberof(array) ((int) (sizeof(array) / sizeof((array)[0])))

/* Encodings, by CRuby's accessors. Every encoding prism supports is ASCII
 * compatible, which is why asciicompat is a constant. */
#define rb_ascii8bit_encoding() PM_ENCODING_ASCII_8BIT_ENTRY
#define rb_utf8_encoding() PM_ENCODING_UTF_8_ENTRY
#define rb_usascii_encoding() PM_ENCODING_US_ASCII_ENTRY
#define rb_enc_name(enc) ((enc)->name)
#define rb_enc_asciicompat(enc) 1
#define rb_enc_isascii(c, enc) ISASCII(c)
#define rb_enc_isalnum(c, enc) ISALNUM(c)
#define rb_enc_isspace(c, enc) ISSPACE(c)
#define rb_enc_mbminlen(enc) 1
#define rb_enc_mbmaxlen(enc) ((enc)->multibyte ? 4 : 1)

/* The string-type node type enum, kept with CRuby's names and order. The
 * grammar and the helpers dispatch on these; they are the fork's own and no
 * longer index into CRuby's node tables. */
enum node_type {
    NODE_SCOPE, NODE_BLOCK, NODE_IF, NODE_UNLESS, NODE_CASE, NODE_CASE2,
    NODE_CASE3, NODE_WHEN, NODE_IN, NODE_WHILE, NODE_UNTIL, NODE_ITER,
    NODE_FOR, NODE_FOR_MASGN, NODE_BREAK, NODE_NEXT, NODE_REDO, NODE_RETRY,
    NODE_BEGIN, NODE_RESCUE, NODE_RESBODY, NODE_ENSURE, NODE_AND, NODE_OR,
    NODE_MASGN, NODE_LASGN, NODE_DASGN, NODE_GASGN, NODE_IASGN, NODE_CDECL,
    NODE_CVASGN, NODE_OP_ASGN1, NODE_OP_ASGN2, NODE_OP_ASGN_AND,
    NODE_OP_ASGN_OR, NODE_OP_CDECL, NODE_CALL, NODE_OPCALL, NODE_FCALL,
    NODE_VCALL, NODE_QCALL, NODE_SUPER, NODE_ZSUPER, NODE_LIST, NODE_ZLIST,
    NODE_HASH, NODE_RETURN, NODE_YIELD, NODE_LVAR, NODE_DVAR, NODE_GVAR,
    NODE_IVAR, NODE_CONST, NODE_CVAR, NODE_NTH_REF, NODE_BACK_REF, NODE_MATCH,
    NODE_MATCH2, NODE_MATCH3, NODE_INTEGER, NODE_FLOAT, NODE_RATIONAL,
    NODE_IMAGINARY, NODE_STR, NODE_DSTR, NODE_XSTR, NODE_DXSTR, NODE_EVSTR,
    NODE_REGX, NODE_DREGX, NODE_ONCE, NODE_ARGS, NODE_ARGS_AUX, NODE_OPT_ARG,
    NODE_KW_ARG, NODE_POSTARG, NODE_ARGSCAT, NODE_ARGSPUSH, NODE_SPLAT,
    NODE_BLOCK_PASS, NODE_DEFN, NODE_DEFS, NODE_ALIAS, NODE_VALIAS,
    NODE_UNDEF, NODE_CLASS, NODE_MODULE, NODE_SCLASS, NODE_COLON2,
    NODE_COLON3, NODE_DOT2, NODE_DOT3, NODE_FLIP2, NODE_FLIP3, NODE_SELF,
    NODE_NIL, NODE_TRUE, NODE_FALSE, NODE_ERRINFO, NODE_DEFINED, NODE_POSTEXE,
    NODE_SYM, NODE_DSYM, NODE_ATTRASGN, NODE_LAMBDA, NODE_ARYPTN, NODE_HSHPTN,
    NODE_FNDPTN, NODE_ERROR, NODE_LINE, NODE_FILE, NODE_ENCODING, NODE_LAST
};

/* All of CRuby's per-type node aliases collapse onto pm_node_t while the
 * bootstrap stubs are in place; each sharpens to its prism node or builder
 * type when the constructors that produce it are ported. */
typedef pm_node_t rb_node_scope_t, rb_node_block_t, rb_node_if_t,
    rb_node_unless_t, rb_node_when_t, rb_node_in_t, rb_node_iter_t,
    rb_node_for_t, rb_node_for_masgn_t, rb_node_retry_t, rb_node_begin_t,
    rb_node_rescue_t, rb_node_resbody_t, rb_node_ensure_t, rb_node_masgn_t,
    rb_node_lasgn_t, rb_node_dasgn_t, rb_node_gasgn_t, rb_node_iasgn_t,
    rb_node_cdecl_t, rb_node_cvasgn_t, rb_node_op_asgn1_t, rb_node_op_asgn2_t,
    rb_node_op_asgn_and_t, rb_node_op_asgn_or_t, rb_node_op_cdecl_t,
    rb_node_call_t, rb_node_opcall_t, rb_node_fcall_t, rb_node_vcall_t,
    rb_node_qcall_t, rb_node_super_t, rb_node_zsuper_t, rb_node_list_t,
    rb_node_zlist_t, rb_node_hash_t, rb_node_return_t, rb_node_yield_t,
    rb_node_lvar_t, rb_node_dvar_t, rb_node_gvar_t, rb_node_ivar_t,
    rb_node_const_t, rb_node_cvar_t, rb_node_nth_ref_t, rb_node_back_ref_t,
    rb_node_match2_t, rb_node_match3_t, rb_node_integer_t, rb_node_float_t,
    rb_node_rational_t, rb_node_imaginary_t, rb_node_str_t, rb_node_dstr_t,
    rb_node_evstr_t, rb_node_once_t, rb_node_args_t, rb_node_args_aux_t,
    rb_node_opt_arg_t, rb_node_kw_arg_t, rb_node_postarg_t, rb_node_argscat_t,
    rb_node_argspush_t, rb_node_splat_t, rb_node_block_pass_t, rb_node_defn_t,
    rb_node_defs_t, rb_node_alias_t, rb_node_valias_t, rb_node_undef_t,
    rb_node_class_t, rb_node_module_t, rb_node_sclass_t, rb_node_colon2_t,
    rb_node_colon3_t, rb_node_self_t, rb_node_nil_t, rb_node_true_t,
    rb_node_false_t, rb_node_errinfo_t, rb_node_defined_t, rb_node_postexe_t,
    rb_node_sym_t, rb_node_attrasgn_t, rb_node_lambda_t, rb_node_aryptn_t,
    rb_node_hshptn_t, rb_node_fndptn_t, rb_node_line_t, rb_node_file_t,
    rb_node_encoding_t, rb_node_error_t, rb_node_exits_t,
    rb_node_break_t, rb_node_next_t, rb_node_redo_t, rb_node_while_t,
    rb_node_until_t, rb_node_case_t, rb_node_case2_t, rb_node_case3_t,
    rb_node_and_t, rb_node_or_t, rb_node_dot2_t, rb_node_dot3_t,
    rb_node_flip2_t, rb_node_flip3_t, rb_node_match_t, rb_node_xstr_t,
    rb_node_dxstr_t, rb_node_regx_t, rb_node_dregx_t, rb_node_dsym_t;

/* Local variable tables attached to scopes. Becomes a pm_constant_id_list_t
 * when scope construction is ported. */
typedef struct rb_ast_id_table {
    int size;
    ID ids[FLEX_ARY_LEN];
} rb_ast_id_table_t;

/* The hash tables the parser keys by name or literal (pattern variable
 * tables, duplicate-key warnings, case/when labels). Everything that touches
 * them is behind stubs until those features are ported, so the type is
 * opaque and the operations are inert. */
typedef struct pm_yst_table st_table;
typedef uintptr_t st_data_t;
typedef int st_index_t;
#define st_free_table(table) ((void) (table))

/* Interning. The second argument to pm_yid_intern is the constant pool the
 * prism parser owns; `p` is in scope at every use site, as it is for CRuby's
 * own implicit-parser macros like tok(). */
#define rb_intern3(name, len, enc) pm_yid_intern(&p->pm->metadata_arena, &p->pm->constant_pool, (const uint8_t *) (name), (size_t) (len), (enc))
#define rb_intern(name) rb_intern3((name), strlen(name), p->enc)
#define rb_id_attrset(id) pm_yid_attrset(&p->pm->metadata_arena, &p->pm->constant_pool, (id))
#define is_notop_id(id) pm_yid_is_notop(id)
#define is_local_id(id) pm_yid_is_local(id)
#define is_global_id(id) pm_yid_is_global(id)
#define is_instance_id(id) pm_yid_is_instance(id)
#define is_attrset_id(id) (((id) == idASET) || pm_yid_is_attrset(id))
#define is_const_id(id) pm_yid_is_const(id)
#define is_class_id(id) pm_yid_is_class(id)
#define is_junk_id(id) pm_yid_is_internal(id)
#define id_type(id) pm_yid_type(id)

/* The static ID constants (idASET, idFWD_REST, keyword token numbers). id.h is
 * the same generated table CRuby compiles, vendored; its values agree with
 * defs/id.def, which tool/id2token.rb also reads. */
#include "id.h"

/* The lexer states, verbatim from CRuby's internal/ruby_parser.h: the lexer's
 * dispatch is built out of these. */
enum lex_state_bits {
    EXPR_BEG_bit,		/* ignore newline, +/- is a sign. */
    EXPR_END_bit,		/* newline significant, +/- is an operator. */
    EXPR_ENDARG_bit,		/* ditto, and unbound braces. */
    EXPR_ENDFN_bit,		/* ditto, and unbound braces. */
    EXPR_ARG_bit,		/* newline significant, +/- is an operator. */
    EXPR_CMDARG_bit,		/* newline significant, +/- is an operator. */
    EXPR_MID_bit,		/* newline significant, +/- is an operator. */
    EXPR_FNAME_bit,		/* ignore newline, no reserved words. */
    EXPR_DOT_bit,		/* right after `.', `&.' or `::', no reserved words. */
    EXPR_CLASS_bit,		/* immediate after `class', no here document. */
    EXPR_LABEL_bit,		/* flag bit, label is allowed. */
    EXPR_LABELED_bit,		/* flag bit, just after a label. */
    EXPR_FITEM_bit,		/* symbol literal as FNAME. */
    EXPR_MAX_STATE
};
enum lex_state_e {
#define DEF_EXPR(n) EXPR_##n = (1 << EXPR_##n##_bit)
    DEF_EXPR(BEG),
    DEF_EXPR(END),
    DEF_EXPR(ENDARG),
    DEF_EXPR(ENDFN),
    DEF_EXPR(ARG),
    DEF_EXPR(CMDARG),
    DEF_EXPR(MID),
    DEF_EXPR(FNAME),
    DEF_EXPR(DOT),
    DEF_EXPR(CLASS),
    DEF_EXPR(LABEL),
    DEF_EXPR(LABELED),
    DEF_EXPR(FITEM),
    EXPR_VALUE = EXPR_BEG,
    EXPR_BEG_ANY  =  (EXPR_BEG | EXPR_MID | EXPR_CLASS),
    EXPR_ARG_ANY  =  (EXPR_ARG | EXPR_CMDARG),
    EXPR_END_ANY  =  (EXPR_END | EXPR_ENDARG | EXPR_ENDFN),
    EXPR_NONE = 0
};

/* String literal / heredoc terminator state, verbatim from CRuby's
 * internal/parse.h. The one change is heredoc's lastline: with the zero-copy
 * line reader it is a slice of the source, so restoring it restores exact
 * byte offsets. */
typedef struct rb_strterm_literal_struct {
    long nest;
    int func;	    /* STR_FUNC_* (e.g., STR_FUNC_ESCAPE and STR_FUNC_EXPAND) */
    int paren;	    /* '(' of `%q(...)` */
    int term;	    /* ')' of `%q(...)` */
} rb_strterm_literal_t;

typedef struct rb_strterm_heredoc_struct {
    rb_parser_string_t *lastline;	/* the string of line that contains `<<"END"` */
    long offset;	/* the column of END in `<<"END"` */
    int sourceline;	/* lineno of the line that contains `<<"END"` */
    unsigned length;	/* the length of END in `<<"END"` */
    uint8_t quote;
    uint8_t func;
} rb_strterm_heredoc_t;

#define HERETERM_LENGTH_MAX UINT_MAX

typedef struct rb_strterm_struct {
    bool heredoc;
    union {
        rb_strterm_literal_t literal;
        rb_strterm_heredoc_t heredoc;
    } u;
} rb_strterm_t;

/* Node accessors. The tree under construction is prism's, so CRuby's header
 * fields do not exist; the accessors are inert until the constructs that read
 * them are ported. RNODE casts are identity: every rb_node_xxx_t is pm_node_t
 * while the bootstrap stubs are in place. */
#define nd_type(n) ((enum node_type) NODE_LAST)
#define nd_type_p(n, t) 0
#define nd_line(n) 0
#define nd_set_line(n, l) ((void) 0)
#define nd_first_lineno(n) 0
#define nd_first_column(n) 0
#define nd_last_lineno(n) 0
#define nd_last_column(n) 0
#define RNODE(obj) ((NODE *) (obj))

/* Misc CRuby spellings. */
#define MAYBE_UNUSED(x) x
#define rb_strlen_lit(str) (sizeof(str "") - 1)
#ifndef PRIdPTRDIFF
#define PRIdPTRDIFF "td"
#endif
#ifndef PRIsVALUE
#define PRIsVALUE "s"
#endif

/* Case-insensitive comparisons for magic comments. ASCII-only by design, as
 * CRuby's parser versions are. */
static int
pm_y_strcasecmp(const char *s1, const char *s2) {
    while (*s1 || *s2) {
        int c1 = (unsigned char) *s1++;
        int c2 = (unsigned char) *s2++;
        if ('A' <= c1 && c1 <= 'Z') c1 += 'a' - 'A';
        if ('A' <= c2 && c2 <= 'Z') c2 += 'a' - 'A';
        if (c1 != c2) return c1 - c2;
    }
    return 0;
}

static int
pm_y_strncasecmp(const char *s1, const char *s2, size_t n) {
    while (n--) {
        int c1 = (unsigned char) *s1++;
        int c2 = (unsigned char) *s2++;
        if ('A' <= c1 && c1 <= 'Z') c1 += 'a' - 'A';
        if ('A' <= c2 && c2 <= 'Z') c2 += 'a' - 'A';
        if (c1 != c2) return c1 - c2;
        if (!c1) break;
    }
    return 0;
}

/*
 * BOOTSTRAP STUBS. The node-building half of the grammar is ported
 * incrementally; until a construct's helpers are ported, they reduce to this,
 * which records that the parse touched something the backend cannot build
 * yet. The parse still runs -- the lexer and the grammar's state handling are
 * real -- but the resulting tree is incomplete, and the diagnostic makes that
 * impossible to miss.
 */
/* KNOWN LEAK while stubs remain: strings and numeric spellings the lexer
 * hands to stubbed constructors (NEW_STR, NEW_INTEGER, ...) are dropped
 * without an owner. The real constructors take ownership as they are ported,
 * which is also what removes the stubs themselves. */
#define YSTUB(name) \
    pm_yparse_stub(p, name)

static void pm_yparse_stub(struct parser_params *p, const char *name);

/* Defined in the driver section at the end of this file; the lexer publishes
 * token locations through them via the RUBY_SET_YYLLOC macros. */
static YYLTYPE *rb_parser_set_location_from_strterm_heredoc(struct parser_params *p, rb_strterm_heredoc_t *here, YYLTYPE *yylloc);
static YYLTYPE *rb_parser_set_location_of_heredoc_end(struct parser_params *p, YYLTYPE *yylloc);
static YYLTYPE *rb_parser_set_location_of_none(struct parser_params *p, YYLTYPE *yylloc);
static YYLTYPE *rb_parser_set_location(struct parser_params *p, YYLTYPE *yylloc);


/* Numeric literal classification, from rubyparser.h. The imaginary node adds
 * imaginary_literal in CRuby via its own field type; the lexer only needs the
 * base three plus that one. */
enum rb_numeric_type {
    integer_literal,
    float_literal,
    rational_literal,
    imaginary_literal
};

/* Shareable-constant-value modes, from rubyparser.h. */
enum rb_parser_shareability {
    rb_parser_shareable_none,
    rb_parser_shareable_literal,
    rb_parser_shareable_copy,
    rb_parser_shareable_everything
};

/* From parser_node.h: merge two locations into begin-of-first..end-of-second. */
static inline rb_code_location_t
code_loc_gen(const rb_code_location_t *loc1, const rb_code_location_t *loc2)
{
    rb_code_location_t loc;
    loc.beg = loc1->beg;
    loc.end = loc2->end;
    return loc;
}

/* Regexp compilation is deferred (prism's own regexp parser takes over when
 * named captures are ported); these keep the stubbed signatures compiling. */
typedef unsigned char OnigUChar;
typedef void *OnigRegex;
typedef NODE *(*rb_parser_assignable_func)(struct parser_params *p, ID id, NODE *val, const YYLTYPE *loc);
struct rb_args_info;

#define RUBY_SYMBOL_EXPORT_BEGIN
#define RUBY_SYMBOL_EXPORT_END
#define ruby_verbose 0
#define FIXNUM_MAX (LONG_MAX >> 1)

/* Symbol-string round trips: the ID's spelling, as a fresh ystring the
 * caller owns. Defined after the pool helpers; the macro carries `p`. */
static rb_parser_string_t *pm_yid2str(struct parser_params *p, ID id);
#define rb_id2str(id) pm_yid2str(p, (id))
#define rb_id2name(id) ((void) (id), "")
#define rb_sym2id(str) ((str) ? rb_intern3(PM_YSTRING_PTR(str), PM_YSTRING_LEN(str), p->enc) : 0)
#define rb_intern_str(str) rb_sym2id(str)
#define rb_intern2(name, len) rb_intern3((name), (len), p->enc)

/* Strings under their CRuby names. */
#define rb_enc_str_new(ptr, len, enc) pm_ystring_new((ptr), (long) (len), (enc))
#define parser_str_cat(str, ptr, len) pm_ystring_cat((str), (ptr), (long) (len))
#define parser_str_cat_cstr(str, s) pm_ystring_cat((str), (s), (long) strlen(s))

/* The newline flag maps directly onto prism's. */
#define nd_set_fl_newline(n) ((void) ((n) != NULL && ((n)->flags |= PM_NODE_FLAG_NEWLINE)))
static inline void
nd_unset_fl_newline(NODE *n)
{
    if (n == NULL) return;
    /* A statements list keeps its members' markers; only a lone expression
     * loses its (see the embedded-statements constructor). */
    if (PM_NODE_TYPE_P(n, PM_STATEMENTS_NODE)) return;
    n->flags &= (pm_node_flags_t) ~PM_NODE_FLAG_NEWLINE;
}

/* The pattern-matching duplicate tables arrive with the pattern port. */
#define st_init_numtable() NULL

/* Debug/fatal surface. */
#define rb_parser_printf(p, ...) ((void) 0)
#define rb_parser_fatal(p, ...) rb_bug(__VA_ARGS__)
#define rb_fatal(...) rb_bug(__VA_ARGS__)
#define parser_show_error_line(p, loc) ((void) 0)
#define ruby_xfree_sized(ptr, size) xfree_sized((ptr), (size))
#define UNLIKELY(x) (x)
#define LIKELY(x) (x)

/* Encoding odds and ends. */
#define rb_is_usascii_enc(enc) ((const pm_encoding_t *) (enc) == PM_ENCODING_US_ASCII_ENTRY)
#define rb_memcicmp(a, b, n) pm_y_strncasecmp((const char *) (a), (const char *) (b), (size_t) (n))

/* Symbol-name classification: the callers only ask "would this spelling be a
 * valid symbol of this kind"; the lexer has already vetted the characters, so
 * agreeing is correct until dsym validation is ported. */
#define rb_enc_symname_type(name, len, enc, allowed) ((void) (name), (void) (len), pm_y_ctz(allowed))
static inline int
pm_y_ctz(unsigned int bits)
{
    int index = 0;
    while (bits > 1) { bits >>= 1; index++; }
    return index;
}

/* The UTF-8 encoder for \u escapes. Everything else prism supports is a
 * single-byte encoding as far as escape output is concerned. */
static int
rb_enc_codelen(int c, rb_encoding *enc)
{
    if (enc != rb_utf8_encoding()) return 1;
    if (c < 0x80) return 1;
    if (c < 0x800) return 2;
    if (c < 0x10000) return 3;
    return 4;
}

static int
rb_enc_mbcput(int c, void *buf, rb_encoding *enc)
{
    unsigned char *bytes = (unsigned char *) buf;
    int len = rb_enc_codelen(c, enc);

    switch (len) {
      case 1:
        bytes[0] = (unsigned char) c;
        break;
      case 2:
        bytes[0] = (unsigned char) (0xc0 | (c >> 6));
        bytes[1] = (unsigned char) (0x80 | (c & 0x3f));
        break;
      case 3:
        bytes[0] = (unsigned char) (0xe0 | (c >> 12));
        bytes[1] = (unsigned char) (0x80 | ((c >> 6) & 0x3f));
        bytes[2] = (unsigned char) (0x80 | (c & 0x3f));
        break;
      default:
        bytes[0] = (unsigned char) (0xf0 | (c >> 18));
        bytes[1] = (unsigned char) (0x80 | ((c >> 12) & 0x3f));
        bytes[2] = (unsigned char) (0x80 | ((c >> 6) & 0x3f));
        bytes[3] = (unsigned char) (0x80 | (c & 0x3f));
        break;
    }
    return len;
}

/* Number scanning, from CRuby's util.c. */
static unsigned long
ruby_scan_digits(const char *str, long len, int base, size_t *retlen, int *overflow)
{
    const char *start = str;
    unsigned long ret = 0;
    unsigned long mul_overflow = (~(unsigned long) 0) / (unsigned long) base;

    *overflow = 0;
    if (!len) {
        *retlen = 0;
        return 0;
    }

    do {
        int d;
        int c = (unsigned char) *str;
        if (c >= '0' && c <= '9') d = c - '0';
        else if (c >= 'a' && c <= 'z') d = c - 'a' + 10;
        else if (c >= 'A' && c <= 'Z') d = c - 'A' + 10;
        else break;
        if (d >= base) break;

        if (mul_overflow < ret) *overflow = 1;
        ret *= (unsigned long) base;
        if (ret > ret + (unsigned long) d) *overflow = 1;
        ret += (unsigned long) d;
        str++;
    } while (len < 0 || --len);

    *retlen = (size_t) (str - start);
    return ret;
}

static unsigned long
ruby_scan_oct(const char *start, size_t len, size_t *retlen)
{
    int overflow;
    return ruby_scan_digits(start, (long) len, 8, retlen, &overflow);
}

static unsigned long
ruby_scan_hex(const char *start, size_t len, size_t *retlen)
{
    int overflow;
    return ruby_scan_digits(start, (long) len, 16, retlen, &overflow);
}

/* Punctuation global variables ($~, $&, ...), from CRuby's symbol.h. */
static inline int
is_global_name_punct(const int c)
{
    if (c <= 0x20 || 0x7e < c) return 0;
    return strchr("~*$?!@/\\;,.=:<>\"&`'+0", c) != NULL;
}

/* strdup is POSIX, not C99; the numeric literal strings it copies move into
 * prism's integer parsing when numerics are ported. */
static char *
pm_y_strdup(const char *str)
{
    size_t size = strlen(str) + 1;
    char *copy = xmalloc(size);
    if (copy == NULL) abort();
    memcpy(copy, str, size);
    return copy;
}
#define strdup(str) pm_y_strdup(str)

struct rb_iseq_struct;

/* Documented switch fallthroughs inherited from CRuby's lexer. */
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC diagnostic ignored "-Wimplicit-fallthrough"
#endif

#define rb_node_sym_string_val(node) ((void) (node), (rb_parser_string_t *) 0)

/* END ADAPTERS. */

#define NODE_SPECIAL_EMPTY_ARGS ((NODE *)-1)
#define NODE_EMPTY_ARGS_P(node) ((node) == NODE_SPECIAL_EMPTY_ARGS)
#define NODE_SPECIAL_REQUIRED_KEYWORD ((NODE *)-1)
#define NODE_REQUIRED_KEYWORD_P(node) ((node) == NODE_SPECIAL_REQUIRED_KEYWORD)
#define NODE_SPECIAL_NO_NAME_REST     ((NODE *)-1)
#define NODE_NAMED_REST_P(node) ((node) != NODE_SPECIAL_NO_NAME_REST)
#define NODE_SPECIAL_EXCESSIVE_COMMA   ((ID)1)



/* The literal comparison/hash machinery behind the duplicate-hash-key and
 * duplicate-case-label warnings dispatched on CRuby node internals; it
 * returns when those warnings are ported. */

static inline int
parse_isascii(int c)
{
    return '\0' <= c && c <= '\x7f';
}

#undef ISASCII
#define ISASCII parse_isascii

static inline int
parse_isspace(int c)
{
    return c == ' ' || ('\t' <= c && c <= '\r');
}

#undef ISSPACE
#define ISSPACE parse_isspace

static inline int
parse_iscntrl(int c)
{
    return ('\0' <= c && c < ' ') || c == '\x7f';
}

#undef ISCNTRL
#define ISCNTRL(c) parse_iscntrl(c)

static inline int
parse_isupper(int c)
{
    return 'A' <= c && c <= 'Z';
}

static inline int
parse_islower(int c)
{
    return 'a' <= c && c <= 'z';
}

static inline int
parse_isalpha(int c)
{
    return parse_isupper(c) || parse_islower(c);
}

#undef ISALPHA
#define ISALPHA(c) parse_isalpha(c)

static inline int
parse_isdigit(int c)
{
    return '0' <= c && c <= '9';
}

#undef ISDIGIT
#define ISDIGIT(c) parse_isdigit(c)

static inline int
parse_isalnum(int c)
{
    return ISALPHA(c) || ISDIGIT(c);
}

#undef ISALNUM
#define ISALNUM(c) parse_isalnum(c)

static inline int
parse_isxdigit(int c)
{
    return ISDIGIT(c) || ('A' <= c && c <= 'F') || ('a' <= c && c <= 'f');
}

#undef ISXDIGIT
#define ISXDIGIT(c) parse_isxdigit(c)

#undef STRCASECMP
#define STRCASECMP pm_y_strcasecmp

#undef STRNCASECMP
#define STRNCASECMP pm_y_strncasecmp


enum rescue_context {
    before_rescue,
    after_rescue,
    after_else,
    after_ensure,
};

struct lex_context {
    unsigned int in_defined: 1;
    unsigned int in_kwarg: 1;
    unsigned int in_argdef: 1;
    unsigned int in_def: 1;
    unsigned int in_class: 1;
    unsigned int has_trailing_semicolon: 1;
    BITFIELD(enum rb_parser_shareability, shareable_constant_value, 2);
    BITFIELD(enum rescue_context, in_rescue, 2);
    unsigned int cant_return: 1;
    unsigned int in_alt_pattern: 1;
    unsigned int capture_in_pattern: 1;
};

typedef struct RNode_DEF_TEMP rb_node_def_temp_t;


#include "parse.h"

#define NO_LEX_CTXT (struct lex_context){0}

#ifndef WARN_PAST_SCOPE
# define WARN_PAST_SCOPE 0
#endif

#define TAB_WIDTH 8

#define YYLLOC_DEFAULT(Current, Rhs, N)					\
    do									\
      if (N)								\
        {								\
          (Current).beg = YYRHSLOC(Rhs, 1).beg;				\
          (Current).end = YYRHSLOC(Rhs, N).end;				\
        }								\
      else								\
        {                                                               \
          (Current).beg = YYRHSLOC(Rhs, 0).end;                         \
          (Current).end = YYRHSLOC(Rhs, 0).end;                         \
        }                                                               \
    while (0)
#define YY_(Msgid) \
    (((Msgid)[0] == 'm') && (strcmp((Msgid), "memory exhausted") == 0) ? \
     "nesting too deep" : (Msgid))

#define RUBY_SET_YYLLOC_FROM_STRTERM_HEREDOC(Current)			\
    rb_parser_set_location_from_strterm_heredoc(p, &p->lex.strterm->u.heredoc, &(Current))
#define RUBY_SET_YYLLOC_OF_HEREDOC_END(Current)				\
    rb_parser_set_location_of_heredoc_end(p, &(Current))
#define RUBY_SET_YYLLOC_OF_NONE(Current)				\
    rb_parser_set_location_of_none(p, &(Current))
#define RUBY_SET_YYLLOC(Current)					\
    rb_parser_set_location(p, &(Current))
#define RUBY_INIT_YYLLOC() \
    { \
        YOFF(p->lex.ptok), \
        YOFF(p->lex.pcur), \
    }

#define IS_lex_state_for(x, ls)	((x) & (ls))
#define IS_lex_state_all_for(x, ls) (((x) & (ls)) == (ls))
#define IS_lex_state(ls)	IS_lex_state_for(p->lex.state, (ls))
#define IS_lex_state_all(ls)	IS_lex_state_all_for(p->lex.state, (ls))

# define SET_LEX_STATE(ls) \
    parser_set_lex_state(p, ls, __LINE__)
static inline enum lex_state_e parser_set_lex_state(struct parser_params *p, enum lex_state_e ls, int line);

typedef VALUE stack_type;

static const rb_code_location_t NULL_LOC = { 0, 0 };

# define SHOW_BITSTACK(stack, name) ((void)0)
# define BITSTACK_PUSH(stack, n) (((p->stack) = ((p->stack)<<1)|((n)&1)), SHOW_BITSTACK(p->stack, #stack"(push)"))
# define BITSTACK_POP(stack)	 (((p->stack) = (p->stack) >> 1), SHOW_BITSTACK(p->stack, #stack"(pop)"))
# define BITSTACK_SET_P(stack)	 (SHOW_BITSTACK(p->stack, #stack), (p->stack)&1)
# define BITSTACK_SET(stack, n)	 ((p->stack)=(n), SHOW_BITSTACK(p->stack, #stack"(set)"))

/* A flag to identify keyword_do_cond, "do" keyword after condition expression.
   Examples: `while ... do`, `until ... do`, and `for ... in ... do` */
#define COND_PUSH(n)	BITSTACK_PUSH(cond_stack, (n))
#define COND_POP()	BITSTACK_POP(cond_stack)
#define COND_P()	BITSTACK_SET_P(cond_stack)
#define COND_SET(n)	BITSTACK_SET(cond_stack, (n))

/* A flag to identify keyword_do_block; "do" keyword after command_call.
   Example: `foo 1, 2 do`. */
#define CMDARG_PUSH(n)	BITSTACK_PUSH(cmdarg_stack, (n))
#define CMDARG_POP()	BITSTACK_POP(cmdarg_stack)
#define CMDARG_P()	BITSTACK_SET_P(cmdarg_stack)
#define CMDARG_SET(n)	BITSTACK_SET(cmdarg_stack, (n))

struct vtable {
    ID *tbl;
    int pos;
    int capa;
    struct vtable *prev;
};

struct local_vars {
    struct vtable *args;
    struct vtable *vars;
    struct vtable *used;
# if WARN_PAST_SCOPE
    struct vtable *past;
# endif
    struct local_vars *prev;
    struct {
        NODE *outer, *inner, *current;
    } numparam;
    NODE *it;
};

typedef struct rb_locations_lambda_body_t {
    NODE *node;
    YYLTYPE opening_loc;
    YYLTYPE closing_loc;
} rb_locations_lambda_body_t;

enum {
    ORDINAL_PARAM = -1,
    NO_PARAM = 0,
    NUMPARAM_MAX = 9,
};

#define DVARS_INHERIT ((void*)1)
#define DVARS_TOPSCOPE NULL
#define DVARS_TERMINAL_P(tbl) ((tbl) == DVARS_INHERIT || (tbl) == DVARS_TOPSCOPE)

typedef struct token_info {
    const char *token;
    rb_code_position_t beg;
    int indent;
    int nonspc;
    struct token_info *next;
} token_info;

typedef struct end_expect_token_locations {
    const rb_code_position_t *pos;
    struct end_expect_token_locations *prev;
} end_expect_token_locations_t;

#define AFTER_HEREDOC_WITHOUT_TERMINATOR ((rb_parser_string_t *)1)

/*
    Structure of Lexer Buffer:

 lex.pbeg     lex.ptok     lex.pcur     lex.pend
    |            |            |            |
    |------------+------------+------------|
                 |<---------->|
                     token
*/
struct parser_params {
    YYSTYPE *lval;
    YYLTYPE *yylloc;

    /* The prism parser this parse reports into: the arenas every allocation
     * that outlives the parse comes from, the constant pool names intern into,
     * the diagnostic lists, and the source text itself. */
    pm_parser_t *pm;

    struct {
        rb_strterm_t *strterm;
        /* The read cursor of the line reader: the first byte of the next line
         * lex_getline will hand out. Advances monotonically through
         * pm->start..pm->end even while heredocs rewind the current line. */
        const char *gets_cursor;
        rb_parser_string_t *lastline;
        rb_parser_string_t *nextline;
        const char *pbeg;
        const char *pcur;
        const char *pend;
        const char *ptok;
        enum lex_state_e state;
        /* track the nest level of any parens "()[]{}" */
        int paren_nest;
        /* keep p->lex.paren_nest at the beginning of lambda "->" to detect tLAMBEG and keyword_do_LAMBDA */
        int lpar_beg;
        /* track the nest level of only braces "{}" */
        int brace_nest;
    } lex;
    stack_type cond_stack;
    stack_type cmdarg_stack;

    /* Inert: nothing sets delayed.token since the token event plumbing was
     * dropped, so the guards reading it are permanently false. */
    struct {
        rb_parser_string_t *token;
        int beg_line;
        int beg_col;
        int end_line;
        int end_col;
    } delayed;

    /* fork: the parenthesis locations of the paren_args just reduced, consumed
     * by the call that attaches those arguments. A single slot suffices: the
     * grammar reduces an inner call completely before the enclosing
     * paren_args closes, so set/consume pairs never interleave. */
    struct {
        YYLTYPE opening;
        YYLTYPE closing;
        unsigned int set: 1;
    } yparens;

    /* fork: the `do` of the expr_value_do just reduced, for while/until. */
    struct {
        YYLTYPE loc;
        unsigned int set: 1;
    } ydo;

    /* fork: parameter nodes built at the marker reductions (where the
     * `*`/`**`/`&` and name locations exist), consumed by new_args and
     * new_args_tail, which upstream only sees the IDs. */
    NODE *yrest_param;
    NODE *ykwrest_param;
    NODE *yblock_param;

    /* fork: a &block argument parked by arg_blk_pass for the call about to
     * consume its arguments; prism hangs it on the call, not the list. */
    NODE *yblock_pass;
    int tokidx;
    int toksiz;
    int heredoc_end;
    int heredoc_indent;
    int heredoc_line_indent;
    char *tokenbuf;
    struct local_vars *lvtbl;
    st_table *pvtbl;
    st_table *pktbl;
    int line_count;
    int ruby_sourceline;	/* current line no. */
    rb_encoding *enc;
    token_info *token_info;
    st_table *case_labels;
    rb_node_exits_t *exits;

    int node_id;

    st_table *warn_duplicate_keys_table;

    int max_numparam;
    ID it_id;

    struct lex_context ctxt;

    NODE *eval_tree_begin;
    NODE *eval_tree;

    /* compile_option */
    signed int frozen_string_literal:2; /* -1: not specified, 0: false, 1: true */

    unsigned int command_start:1;
    unsigned int eofp: 1;
    unsigned int ruby__end__seen: 1;
    unsigned int debug: 1;
    unsigned int has_shebang: 1;
    unsigned int token_seen: 1;
    unsigned int token_info_enabled: 1;
    unsigned int error_p: 1;
    unsigned int cr_seen: 1;

    unsigned int do_print: 1;
    unsigned int do_loop: 1;
    unsigned int do_chomp: 1;
    unsigned int do_split: 1;
};

#define NUMPARAM_ID_P(id) numparam_id_p(p, id)
#define NUMPARAM_ID_TO_IDX(id) (unsigned int)(((id) >> ID_SCOPE_SHIFT) - (tNUMPARAM_1 - 1))
#define NUMPARAM_IDX_TO_ID(idx) TOKEN2LOCALID((tNUMPARAM_1 - 1 + (idx)))
static int
numparam_id_p(struct parser_params *p, ID id)
{
    if (!is_local_id(id) || id < (tNUMPARAM_1 << ID_SCOPE_SHIFT)) return 0;
    unsigned int idx = NUMPARAM_ID_TO_IDX(id);
    return idx > 0 && idx <= NUMPARAM_MAX;
}
static void numparam_name(struct parser_params *p, ID id);

static void
after_shift(struct parser_params *p)
{
}

static void
before_reduce(int len, struct parser_params *p)
{
}

static void
after_reduce(int len, struct parser_params *p)
{
}

static void
after_shift_error_token(struct parser_params *p)
{
}

static void
after_pop_stack(int len, struct parser_params *p)
{
}

#define intern_cstr(n,l,en) rb_intern3(n,l,en)

#define STRING_NEW0() rb_parser_encoding_string_new(p,0,0,p->enc)

#define STR_NEW(ptr,len) rb_enc_str_new((ptr),(len),p->enc)
#define STR_NEW0() rb_enc_str_new(0,0,p->enc)
#define STR_NEW2(ptr) rb_enc_str_new((ptr),strlen(ptr),p->enc)
#define STR_NEW3(ptr,len,e,func) parser_str_new(p, (ptr),(len),(e),(func),p->enc)
#define TOK_INTERN() intern_cstr(tok(p), toklen(p), p->enc)
#define VALID_SYMNAME_P(s, l, enc, type) (rb_enc_symname_type(s, l, enc, (1U<<(type))) == (int)(type))

static inline int
char_at_end(struct parser_params *p, VALUE str, int when_empty)
{
    return when_empty;
}

static void
pop_pvtbl(struct parser_params *p, st_table *tbl)
{
    st_free_table(p->pvtbl);
    p->pvtbl = tbl;
}

static void
pop_pktbl(struct parser_params *p, st_table *tbl)
{
    if (p->pktbl) st_free_table(p->pktbl);
    p->pktbl = tbl;
}

#define STRING_BUF_DEFAULT_LEN 16




static void flush_debug_buffer(struct parser_params *p, VALUE out, VALUE str);

static void
debug_end_expect_token_locations(struct parser_params *p, const char *name)
{
    /* debug output is not ported */
}

static void
push_end_expect_token_locations(struct parser_params *p, const rb_code_position_t *pos)
{
    /* error tolerance is not ported */
}

static void
pop_end_expect_token_locations(struct parser_params *p)
{
    /* error tolerance is not ported */
}

static end_expect_token_locations_t *
peek_end_expect_token_locations(struct parser_params *p)
{
    return NULL;
}

static const char *
parser_token2char(struct parser_params *p, enum yytokentype tok)
{
    switch ((int) tok) {
#define TOKEN2CHAR(tok) case tok: return (#tok);
#define TOKEN2CHAR2(tok, name) case tok: return (name);
      TOKEN2CHAR2(' ', "word_sep");
      TOKEN2CHAR2('!', "!")
      TOKEN2CHAR2('%', "%");
      TOKEN2CHAR2('&', "&");
      TOKEN2CHAR2('*', "*");
      TOKEN2CHAR2('+', "+");
      TOKEN2CHAR2('-', "-");
      TOKEN2CHAR2('/', "/");
      TOKEN2CHAR2('<', "<");
      TOKEN2CHAR2('=', "=");
      TOKEN2CHAR2('>', ">");
      TOKEN2CHAR2('?', "?");
      TOKEN2CHAR2('^', "^");
      TOKEN2CHAR2('|', "|");
      TOKEN2CHAR2('~', "~");
      TOKEN2CHAR2(':', ":");
      TOKEN2CHAR2(',', ",");
      TOKEN2CHAR2('.', ".");
      TOKEN2CHAR2(';', ";");
      TOKEN2CHAR2('`', "`");
      TOKEN2CHAR2('\n', "nl");
      TOKEN2CHAR2('{', "\"{\"");
      TOKEN2CHAR2('}', "\"}\"");
      TOKEN2CHAR2('[', "\"[\"");
      TOKEN2CHAR2(']', "\"]\"");
      TOKEN2CHAR2('(', "\"(\"");
      TOKEN2CHAR2(')', "\")\"");
      TOKEN2CHAR2('\\', "backslash");
      TOKEN2CHAR(keyword_class);
      TOKEN2CHAR(keyword_module);
      TOKEN2CHAR(keyword_def);
      TOKEN2CHAR(keyword_undef);
      TOKEN2CHAR(keyword_begin);
      TOKEN2CHAR(keyword_rescue);
      TOKEN2CHAR(keyword_ensure);
      TOKEN2CHAR(keyword_end);
      TOKEN2CHAR(keyword_if);
      TOKEN2CHAR(keyword_unless);
      TOKEN2CHAR(keyword_then);
      TOKEN2CHAR(keyword_elsif);
      TOKEN2CHAR(keyword_else);
      TOKEN2CHAR(keyword_case);
      TOKEN2CHAR(keyword_when);
      TOKEN2CHAR(keyword_while);
      TOKEN2CHAR(keyword_until);
      TOKEN2CHAR(keyword_for);
      TOKEN2CHAR(keyword_break);
      TOKEN2CHAR(keyword_next);
      TOKEN2CHAR(keyword_redo);
      TOKEN2CHAR(keyword_retry);
      TOKEN2CHAR(keyword_in);
      TOKEN2CHAR(keyword_do);
      TOKEN2CHAR(keyword_do_cond);
      TOKEN2CHAR(keyword_do_block);
      TOKEN2CHAR(keyword_do_LAMBDA);
      TOKEN2CHAR(keyword_return);
      TOKEN2CHAR(keyword_yield);
      TOKEN2CHAR(keyword_super);
      TOKEN2CHAR(keyword_self);
      TOKEN2CHAR(keyword_nil);
      TOKEN2CHAR(keyword_true);
      TOKEN2CHAR(keyword_false);
      TOKEN2CHAR(keyword_and);
      TOKEN2CHAR(keyword_or);
      TOKEN2CHAR(keyword_not);
      TOKEN2CHAR(modifier_if);
      TOKEN2CHAR(modifier_unless);
      TOKEN2CHAR(modifier_while);
      TOKEN2CHAR(modifier_until);
      TOKEN2CHAR(modifier_rescue);
      TOKEN2CHAR(keyword_alias);
      TOKEN2CHAR(keyword_defined);
      TOKEN2CHAR(keyword_BEGIN);
      TOKEN2CHAR(keyword_END);
      TOKEN2CHAR(keyword__LINE__);
      TOKEN2CHAR(keyword__FILE__);
      TOKEN2CHAR(keyword__ENCODING__);
      TOKEN2CHAR(tIDENTIFIER);
      TOKEN2CHAR(tFID);
      TOKEN2CHAR(tGVAR);
      TOKEN2CHAR(tIVAR);
      TOKEN2CHAR(tCONSTANT);
      TOKEN2CHAR(tCVAR);
      TOKEN2CHAR(tLABEL);
      TOKEN2CHAR(tINTEGER);
      TOKEN2CHAR(tFLOAT);
      TOKEN2CHAR(tRATIONAL);
      TOKEN2CHAR(tIMAGINARY);
      TOKEN2CHAR(tCHAR);
      TOKEN2CHAR(tNTH_REF);
      TOKEN2CHAR(tBACK_REF);
      TOKEN2CHAR(tSTRING_CONTENT);
      TOKEN2CHAR(tREGEXP_END);
      TOKEN2CHAR(tDUMNY_END);
      TOKEN2CHAR(tSP);
      TOKEN2CHAR(tUPLUS);
      TOKEN2CHAR(tUMINUS);
      TOKEN2CHAR(tPOW);
      TOKEN2CHAR(tCMP);
      TOKEN2CHAR(tEQ);
      TOKEN2CHAR(tEQQ);
      TOKEN2CHAR(tNEQ);
      TOKEN2CHAR(tGEQ);
      TOKEN2CHAR(tLEQ);
      TOKEN2CHAR(tANDOP);
      TOKEN2CHAR(tOROP);
      TOKEN2CHAR(tMATCH);
      TOKEN2CHAR(tNMATCH);
      TOKEN2CHAR(tDOT2);
      TOKEN2CHAR(tDOT3);
      TOKEN2CHAR(tBDOT2);
      TOKEN2CHAR(tBDOT3);
      TOKEN2CHAR(tAREF);
      TOKEN2CHAR(tASET);
      TOKEN2CHAR(tLSHFT);
      TOKEN2CHAR(tRSHFT);
      TOKEN2CHAR(tANDDOT);
      TOKEN2CHAR(tCOLON2);
      TOKEN2CHAR(tCOLON3);
      TOKEN2CHAR(tOP_ASGN);
      TOKEN2CHAR(tASSOC);
      TOKEN2CHAR(tLPAREN);
      TOKEN2CHAR(tLPAREN_ARG);
      TOKEN2CHAR(tLBRACK);
      TOKEN2CHAR(tLBRACE);
      TOKEN2CHAR(tLBRACE_ARG);
      TOKEN2CHAR(tSTAR);
      TOKEN2CHAR(tDSTAR);
      TOKEN2CHAR(tAMPER);
      TOKEN2CHAR(tLAMBDA);
      TOKEN2CHAR(tSYMBEG);
      TOKEN2CHAR(tSTRING_BEG);
      TOKEN2CHAR(tXSTRING_BEG);
      TOKEN2CHAR(tREGEXP_BEG);
      TOKEN2CHAR(tWORDS_BEG);
      TOKEN2CHAR(tQWORDS_BEG);
      TOKEN2CHAR(tSYMBOLS_BEG);
      TOKEN2CHAR(tQSYMBOLS_BEG);
      TOKEN2CHAR(tSTRING_END);
      TOKEN2CHAR(tSTRING_DEND);
      TOKEN2CHAR(tSTRING_DBEG);
      TOKEN2CHAR(tSTRING_DVAR);
      TOKEN2CHAR(tLAMBEG);
      TOKEN2CHAR(tLABEL_END);
      TOKEN2CHAR(tIGNORED_NL);
      TOKEN2CHAR(tCOMMENT);
      TOKEN2CHAR(tEMBDOC_BEG);
      TOKEN2CHAR(tEMBDOC);
      TOKEN2CHAR(tEMBDOC_END);
      TOKEN2CHAR(tHEREDOC_BEG);
      TOKEN2CHAR(tHEREDOC_END);
      TOKEN2CHAR(k__END__);
      TOKEN2CHAR(tLOWEST);
      TOKEN2CHAR(tUMINUS_NUM);
      TOKEN2CHAR(tLAST_TOKEN);
#undef TOKEN2CHAR
#undef TOKEN2CHAR2
    }

    rb_bug("parser_token2id: unknown token %d", tok);

    UNREACHABLE_RETURN(0);
}

RBIMPL_ATTR_NONNULL((1, 2, 3))
static int parser_yyerror(struct parser_params*, const YYLTYPE *yylloc, const char*);
RBIMPL_ATTR_NONNULL((1, 2))
static int parser_yyerror0(struct parser_params*, const char*);
#define yyerror0(msg) parser_yyerror0(p, (msg))
#define yyerror1(loc, msg) parser_yyerror(p, (loc), (msg))
#define yyerror(yylloc, p, msg) parser_yyerror(p, yylloc, msg)
#define token_flush(ptr) ((ptr)->lex.ptok = (ptr)->lex.pcur)
#define lex_goto_eol(p) ((p)->lex.pcur = (p)->lex.pend)
#define lex_eol_p(p) lex_eol_n_p(p, 0)
#define lex_eol_n_p(p,n) lex_eol_ptr_n_p(p, (p)->lex.pcur, n)
#define lex_eol_ptr_p(p,ptr) lex_eol_ptr_n_p(p,ptr,0)
#define lex_eol_ptr_n_p(p,ptr,n) ((ptr)+(n) >= (p)->lex.pend)

static void token_info_setup(token_info *ptinfo, const char *ptr, const rb_code_location_t *loc);
static void token_info_push(struct parser_params*, const char *token, const rb_code_location_t *loc);
static void token_info_pop(struct parser_params*, const char *token, const rb_code_location_t *loc);
static void token_info_warn(struct parser_params *p, const char *token, token_info *ptinfo_beg, int same, const rb_code_location_t *loc);
static void token_info_drop(struct parser_params *p, const char *token, rb_code_position_t beg_pos);

#define compile_for_eval	(0)

#define token_column		((int)(p->lex.ptok - p->lex.pbeg))

#define CALL_Q_P(q) ((q) == tANDDOT)
#define NEW_QCALL(q,r,m,a,loc) (CALL_Q_P(q) ? NEW_QCALL0(r,m,a,loc) : NEW_CALL(r,m,a,loc))

#define lambda_beginning_p() (p->lex.lpar_beg == p->lex.paren_nest)

static enum yytokentype yylex(YYSTYPE*, YYLTYPE*, struct parser_params*);

static inline void
rb_discard_node(struct parser_params *p, NODE *n)
{
    /* prism nodes are arena-allocated; there is nothing to return. */
}

static rb_node_scope_t *rb_node_scope_new(struct parser_params *p, rb_node_args_t *nd_args, NODE *nd_body, NODE *nd_parent, const YYLTYPE *loc);
static rb_node_scope_t *rb_node_scope_new2(struct parser_params *p, rb_ast_id_table_t *nd_tbl, rb_node_args_t *nd_args, NODE *nd_body, NODE *nd_parent, const YYLTYPE *loc);
static rb_node_block_t *rb_node_block_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc);
static rb_node_if_t *rb_node_if_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, NODE *nd_else, const YYLTYPE *loc, const YYLTYPE* if_keyword_loc, const YYLTYPE* then_keyword_loc, const YYLTYPE* end_keyword_loc);
static rb_node_unless_t *rb_node_unless_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, NODE *nd_else, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *then_keyword_loc, const YYLTYPE *end_keyword_loc);
static rb_node_case_t *rb_node_case_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc);
static rb_node_case2_t *rb_node_case2_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc);
static rb_node_case3_t *rb_node_case3_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc);
static rb_node_when_t *rb_node_when_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, NODE *nd_next, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *then_keyword_loc);
static rb_node_in_t *rb_node_in_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, NODE *nd_next, const YYLTYPE *loc, const YYLTYPE *in_keyword_loc, const YYLTYPE *then_keyword_loc, const YYLTYPE *operator_loc);
static rb_node_while_t *rb_node_while_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, long nd_state, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *closing_loc);
static rb_node_until_t *rb_node_until_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, long nd_state, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *closing_loc);
static rb_node_iter_t *rb_node_iter_new(struct parser_params *p, rb_node_args_t *nd_args, NODE *nd_body, const YYLTYPE *loc);
static rb_node_for_t *rb_node_for_new(struct parser_params *p, NODE *nd_iter, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *for_keyword_loc, const YYLTYPE *in_keyword_loc, const YYLTYPE *do_keyword_loc, const YYLTYPE *end_keyword_loc);
static rb_node_for_masgn_t *rb_node_for_masgn_new(struct parser_params *p, NODE *nd_var, const YYLTYPE *loc);
static rb_node_retry_t *rb_node_retry_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_begin_t *rb_node_begin_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc);
static rb_node_rescue_t *rb_node_rescue_new(struct parser_params *p, NODE *nd_head, NODE *nd_resq, NODE *nd_else, const YYLTYPE *loc);
static rb_node_resbody_t *rb_node_resbody_new(struct parser_params *p, NODE *nd_args, NODE *nd_exc_var, NODE *nd_body, NODE *nd_next, const YYLTYPE *loc);
static rb_node_ensure_t *rb_node_ensure_new(struct parser_params *p, NODE *nd_head, NODE *nd_ensr, const YYLTYPE *loc);
static rb_node_and_t *rb_node_and_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc, const YYLTYPE *operator_loc);
static rb_node_or_t *rb_node_or_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc, const YYLTYPE *operator_loc);
static rb_node_masgn_t *rb_node_masgn_new(struct parser_params *p, NODE *nd_head, NODE *nd_args, const YYLTYPE *loc);
static rb_node_lasgn_t *rb_node_lasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc);
static rb_node_dasgn_t *rb_node_dasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc);
static rb_node_gasgn_t *rb_node_gasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc);
static rb_node_iasgn_t *rb_node_iasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc);
static rb_node_cdecl_t *rb_node_cdecl_new(struct parser_params *p, ID nd_vid, NODE *nd_value, NODE *nd_else, enum rb_parser_shareability shareability, const YYLTYPE *loc);
static rb_node_cvasgn_t *rb_node_cvasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc);
static rb_node_op_asgn1_t *rb_node_op_asgn1_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *index, NODE *rvalue, const YYLTYPE *loc, const YYLTYPE *call_operator_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc, const YYLTYPE *binary_operator_loc);
static rb_node_op_asgn2_t *rb_node_op_asgn2_new(struct parser_params *p, NODE *nd_recv, NODE *nd_value, ID nd_vid, ID nd_mid, bool nd_aid, const YYLTYPE *loc, const YYLTYPE *call_operator_loc, const YYLTYPE *message_loc, const YYLTYPE *binary_operator_loc);
static rb_node_op_asgn_or_t *rb_node_op_asgn_or_new(struct parser_params *p, NODE *nd_head, NODE *nd_value, const YYLTYPE *loc);
static rb_node_op_asgn_and_t *rb_node_op_asgn_and_new(struct parser_params *p, NODE *nd_head, NODE *nd_value, const YYLTYPE *loc);
static rb_node_op_cdecl_t *rb_node_op_cdecl_new(struct parser_params *p, NODE *nd_head, NODE *nd_value, ID nd_aid, enum rb_parser_shareability shareability, const YYLTYPE *loc);
static rb_node_call_t *rb_node_call_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc);
static rb_node_opcall_t *rb_node_opcall_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc);
static rb_node_fcall_t *rb_node_fcall_new(struct parser_params *p, ID nd_mid, NODE *nd_args, const YYLTYPE *loc);
static rb_node_vcall_t *rb_node_vcall_new(struct parser_params *p, ID nd_mid, const YYLTYPE *loc);
static rb_node_qcall_t *rb_node_qcall_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc);
static rb_node_super_t *rb_node_super_new(struct parser_params *p, NODE *nd_args, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *lparen_loc, const YYLTYPE *rparen_loc);
static rb_node_zsuper_t * rb_node_zsuper_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_list_t *rb_node_list_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc);
static rb_node_list_t *rb_node_list_new2(struct parser_params *p, NODE *nd_head, long nd_alen, NODE *nd_next, const YYLTYPE *loc);
static rb_node_zlist_t *rb_node_zlist_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_hash_t *rb_node_hash_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc);
static rb_node_return_t *rb_node_return_new(struct parser_params *p, NODE *nd_stts, const YYLTYPE *loc, const YYLTYPE *keyword_loc);
static rb_node_yield_t *rb_node_yield_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *lparen_loc, const YYLTYPE *rparen_loc);
static rb_node_lvar_t *rb_node_lvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc);
static rb_node_dvar_t *rb_node_dvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc);
static rb_node_gvar_t *rb_node_gvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc);
static rb_node_ivar_t *rb_node_ivar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc);
static rb_node_const_t *rb_node_const_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc);
static rb_node_cvar_t *rb_node_cvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc);
static rb_node_nth_ref_t *rb_node_nth_ref_new(struct parser_params *p, long nd_nth, const YYLTYPE *loc);
static rb_node_back_ref_t *rb_node_back_ref_new(struct parser_params *p, long nd_nth, const YYLTYPE *loc);
static rb_node_match2_t *rb_node_match2_new(struct parser_params *p, NODE *nd_recv, NODE *nd_value, const YYLTYPE *loc);
static rb_node_match3_t *rb_node_match3_new(struct parser_params *p, NODE *nd_recv, NODE *nd_value, const YYLTYPE *loc);
static rb_node_integer_t * rb_node_integer_new(struct parser_params *p, char* val, int base, const YYLTYPE *loc);
static rb_node_float_t * rb_node_float_new(struct parser_params *p, char* val, const YYLTYPE *loc);
static rb_node_rational_t * rb_node_rational_new(struct parser_params *p, char* val, int base, int seen_point, const YYLTYPE *loc);
static rb_node_imaginary_t * rb_node_imaginary_new(struct parser_params *p, char* val, int base, int seen_point, enum rb_numeric_type, const YYLTYPE *loc);
static rb_node_str_t *rb_node_str_new(struct parser_params *p, rb_parser_string_t *string, const YYLTYPE *loc);
static NODE *string_literal_quotes(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc);
static void pm_yparens_set(struct parser_params *p, const YYLTYPE *opening, const YYLTYPE *closing);
static NODE *pm_yfcall_args(struct parser_params *p, NODE *node, NODE *args, const YYLTYPE *loc);
static pm_statements_node_t *pm_ystatements_ensure(struct parser_params *p, NODE *node);
static pm_statements_node_t *pm_ystatements_opt(struct parser_params *p, NODE *body);
static NODE *pm_yelse(struct parser_params *p, NODE *body, const YYLTYPE *else_loc, const YYLTYPE *loc);
static NODE *pm_yarray_brackets(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc);
static NODE *pm_ybegin_keywords(struct parser_params *p, NODE *node, const YYLTYPE *begin_loc, const YYLTYPE *end_loc);
static NODE *pm_yparentheses(struct parser_params *p, NODE *body, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc);
static void pm_ydef_head(struct parser_params *p, NODE *node, const YYLTYPE *def_loc, const YYLTYPE *operator_loc, const YYLTYPE *name_loc);
static void pm_ydef_parens(struct parser_params *p, NODE *node);
static NODE *pm_ydef_finish(struct parser_params *p, NODE *node, NODE *args, NODE *body, const YYLTYPE *loc, const YYLTYPE *end_loc);
static NODE *pm_yassoc(struct parser_params *p, NODE *key, NODE *value, const YYLTYPE *operator_loc, const YYLTYPE *loc);
static NODE *pm_yassoc_splat(struct parser_params *p, NODE *value, const YYLTYPE *operator_loc, const YYLTYPE *loc);
static NODE *pm_ylabel_symbol(struct parser_params *p, ID label, const YYLTYPE *loc);
static NODE *pm_yhash_braces(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc);
static NODE *pm_ytarget(struct parser_params *p, NODE *node);
static NODE *pm_yarray_finalize(struct parser_params *p, NODE *node);
static void pm_ymulti_parens(struct parser_params *p, NODE *node, const YYLTYPE *lparen, const YYLTYPE *rparen);
static NODE *pm_yensure(struct parser_params *p, NODE *body, const YYLTYPE *ensure_loc, const YYLTYPE *loc);
static NODE *pm_yrescue_finish(struct parser_params *p, NODE *node, const YYLTYPE *keyword_loc, const YYLTYPE *then_loc);
static NODE *pm_yrescue_modifier(struct parser_params *p, NODE *expr, NODE *fallback, const YYLTYPE *keyword_loc, const YYLTYPE *loc);
static NODE *pm_yblock_params(struct parser_params *p, NODE *params, NODE *block_locals, const YYLTYPE *opening, const YYLTYPE *closing);
static NODE *pm_yistr(struct parser_params *p, NODE *part);
static NODE *pm_yindex_call(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing);
static pm_constant_id_t pm_yid2const(struct parser_params *p, ID id);
static void pm_ymarker_param(struct parser_params *p, NODE **slot, int kind, ID name, const YYLTYPE *mark_loc, const YYLTYPE *name_loc);
static NODE *pm_ykw_param(struct parser_params *p, ID label, NODE *value, const YYLTYPE *label_loc, const YYLTYPE *loc);
static void pm_ybegin_stamp_end(NODE *node, pm_location_t end_keyword);
static rb_node_dstr_t *rb_node_dstr_new0(struct parser_params *p, rb_parser_string_t *string, long nd_alen, NODE *nd_next, const YYLTYPE *loc);
static rb_node_dstr_t *rb_node_dstr_new(struct parser_params *p, rb_parser_string_t *string, const YYLTYPE *loc);
static rb_node_xstr_t *rb_node_xstr_new(struct parser_params *p, rb_parser_string_t *string, const YYLTYPE *loc);
static rb_node_dxstr_t *rb_node_dxstr_new(struct parser_params *p, rb_parser_string_t *string, long nd_alen, NODE *nd_next, const YYLTYPE *loc);
static rb_node_evstr_t *rb_node_evstr_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc);
static rb_node_regx_t *rb_node_regx_new(struct parser_params *p, rb_parser_string_t *string, int options, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *content_loc, const YYLTYPE *closing_loc);
static rb_node_once_t *rb_node_once_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc);
static rb_node_args_t *rb_node_args_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_args_aux_t *rb_node_args_aux_new(struct parser_params *p, ID nd_pid, int nd_plen, const YYLTYPE *loc);
static rb_node_opt_arg_t *rb_node_opt_arg_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc);
static rb_node_kw_arg_t *rb_node_kw_arg_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc);
static rb_node_postarg_t *rb_node_postarg_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc);
static rb_node_argscat_t *rb_node_argscat_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc);
static rb_node_argspush_t *rb_node_argspush_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc);
static rb_node_splat_t *rb_node_splat_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc, const YYLTYPE *operator_loc);
static rb_node_block_pass_t *rb_node_block_pass_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *operator_loc);
static rb_node_defn_t *rb_node_defn_new(struct parser_params *p, ID nd_mid, NODE *nd_defn, const YYLTYPE *loc);
static rb_node_defs_t *rb_node_defs_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_defn, const YYLTYPE *loc);
static rb_node_alias_t *rb_node_alias_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc, const YYLTYPE *keyword_loc);
static rb_node_valias_t *rb_node_valias_new(struct parser_params *p, ID nd_alias, ID nd_orig, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *new_loc, const YYLTYPE *old_loc);
static rb_node_undef_t *rb_node_undef_new(struct parser_params *p, NODE *nd_undef, const YYLTYPE *loc);
static rb_node_class_t *rb_node_class_new(struct parser_params *p, NODE *nd_cpath, NODE *nd_body, NODE *nd_super, const YYLTYPE *loc, const YYLTYPE *class_keyword_loc, const YYLTYPE *inheritance_operator_loc, const YYLTYPE *end_keyword_loc);
static rb_node_module_t *rb_node_module_new(struct parser_params *p, NODE *nd_cpath, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *module_keyword_loc, const YYLTYPE *end_keyword_loc);
static rb_node_sclass_t *rb_node_sclass_new(struct parser_params *p, NODE *nd_recv, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *class_keyword_loc, const YYLTYPE *operator_loc, const YYLTYPE *end_keyword_loc);
static rb_node_colon2_t *rb_node_colon2_new(struct parser_params *p, NODE *nd_head, ID nd_mid, const YYLTYPE *loc, const YYLTYPE *delimiter_loc, const YYLTYPE *name_loc);
static rb_node_colon3_t *rb_node_colon3_new(struct parser_params *p, ID nd_mid, const YYLTYPE *loc, const YYLTYPE *delimiter_loc, const YYLTYPE *name_loc);
static rb_node_dot2_t *rb_node_dot2_new(struct parser_params *p, NODE *nd_beg, NODE *nd_end, const YYLTYPE *loc, const YYLTYPE *operator_loc);
static rb_node_dot3_t *rb_node_dot3_new(struct parser_params *p, NODE *nd_beg, NODE *nd_end, const YYLTYPE *loc, const YYLTYPE *operator_loc);
static rb_node_self_t *rb_node_self_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_nil_t *rb_node_nil_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_true_t *rb_node_true_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_false_t *rb_node_false_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_errinfo_t *rb_node_errinfo_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_defined_t *rb_node_defined_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc, const YYLTYPE *keyword_loc);
static rb_node_postexe_t *rb_node_postexe_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc);
static rb_node_sym_t *rb_node_sym_new(struct parser_params *p, rb_parser_string_t *str, const YYLTYPE *loc);
static rb_node_dsym_t *rb_node_dsym_new(struct parser_params *p, rb_parser_string_t *string, long nd_alen, NODE *nd_next, const YYLTYPE *loc);
static rb_node_attrasgn_t *rb_node_attrasgn_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc);
static rb_node_lambda_t *rb_node_lambda_new(struct parser_params *p, rb_node_args_t *nd_args, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *operator_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc);
static rb_node_aryptn_t *rb_node_aryptn_new(struct parser_params *p, NODE *pre_args, NODE *rest_arg, NODE *post_args, const YYLTYPE *loc);
static rb_node_hshptn_t *rb_node_hshptn_new(struct parser_params *p, NODE *nd_pconst, NODE *nd_pkwargs, NODE *nd_pkwrestarg, const YYLTYPE *loc);
static rb_node_fndptn_t *rb_node_fndptn_new(struct parser_params *p, NODE *pre_rest_arg, NODE *args, NODE *post_rest_arg, const YYLTYPE *loc);
static rb_node_line_t *rb_node_line_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_file_t *rb_node_file_new(struct parser_params *p, VALUE str, const YYLTYPE *loc);
static rb_node_error_t *rb_node_error_new(struct parser_params *p, const YYLTYPE *loc);

#define NEW_SCOPE(a,b,c,loc) (NODE *)rb_node_scope_new(p,a,b,c,loc)
#define NEW_SCOPE2(t,a,b,c,loc) (NODE *)rb_node_scope_new2(p,t,a,b,c,loc)
#define NEW_BLOCK(a,loc) (NODE *)rb_node_block_new(p,a,loc)
#define NEW_IF(c,t,e,loc,ik_loc,tk_loc,ek_loc) (NODE *)rb_node_if_new(p,c,t,e,loc,ik_loc,tk_loc,ek_loc)
#define NEW_UNLESS(c,t,e,loc,k_loc,t_loc,e_loc) (NODE *)rb_node_unless_new(p,c,t,e,loc,k_loc,t_loc,e_loc)
#define NEW_CASE(h,b,loc,ck_loc,ek_loc) (NODE *)rb_node_case_new(p,h,b,loc,ck_loc,ek_loc)
#define NEW_CASE2(b,loc,ck_loc,ek_loc) (NODE *)rb_node_case2_new(p,b,loc,ck_loc,ek_loc)
#define NEW_CASE3(h,b,loc,ck_loc,ek_loc) (NODE *)rb_node_case3_new(p,h,b,loc,ck_loc,ek_loc)
#define NEW_WHEN(c,t,e,loc,k_loc,t_loc) (NODE *)rb_node_when_new(p,c,t,e,loc,k_loc,t_loc)
#define NEW_IN(c,t,e,loc,ik_loc,tk_loc,o_loc) (NODE *)rb_node_in_new(p,c,t,e,loc,ik_loc,tk_loc,o_loc)
#define NEW_WHILE(c,b,n,loc,k_loc,c_loc) (NODE *)rb_node_while_new(p,c,b,n,loc,k_loc,c_loc)
#define NEW_UNTIL(c,b,n,loc,k_loc,c_loc) (NODE *)rb_node_until_new(p,c,b,n,loc,k_loc,c_loc)
#define NEW_ITER(a,b,loc) (NODE *)rb_node_iter_new(p,a,b,loc)
#define NEW_FOR(i,b,loc,f_loc,i_loc,d_loc,e_loc) (NODE *)rb_node_for_new(p,i,b,loc,f_loc,i_loc,d_loc,e_loc)
#define NEW_FOR_MASGN(v,loc) (NODE *)rb_node_for_masgn_new(p,v,loc)
#define NEW_RETRY(loc) (NODE *)rb_node_retry_new(p,loc)
#define NEW_BEGIN(b,loc) (NODE *)rb_node_begin_new(p,b,loc)
#define NEW_RESCUE(b,res,e,loc) (NODE *)rb_node_rescue_new(p,b,res,e,loc)
#define NEW_RESBODY(a,v,ex,n,loc) (NODE *)rb_node_resbody_new(p,a,v,ex,n,loc)
#define NEW_ENSURE(b,en,loc) (NODE *)rb_node_ensure_new(p,b,en,loc)
#define NEW_AND(f,s,loc,op_loc) (NODE *)rb_node_and_new(p,f,s,loc,op_loc)
#define NEW_OR(f,s,loc,op_loc) (NODE *)rb_node_or_new(p,f,s,loc,op_loc)
#define NEW_MASGN(l,r,loc)   rb_node_masgn_new(p,l,r,loc)
#define NEW_LASGN(v,val,loc) (NODE *)rb_node_lasgn_new(p,v,val,loc)
#define NEW_DASGN(v,val,loc) (NODE *)rb_node_dasgn_new(p,v,val,loc)
#define NEW_GASGN(v,val,loc) (NODE *)rb_node_gasgn_new(p,v,val,loc)
#define NEW_IASGN(v,val,loc) (NODE *)rb_node_iasgn_new(p,v,val,loc)
#define NEW_CDECL(v,val,path,share,loc) (NODE *)rb_node_cdecl_new(p,v,val,path,share,loc)
#define NEW_CVASGN(v,val,loc) (NODE *)rb_node_cvasgn_new(p,v,val,loc)
#define NEW_OP_ASGN1(r,id,idx,rval,loc,c_op_loc,o_loc,c_loc,b_op_loc) (NODE *)rb_node_op_asgn1_new(p,r,id,idx,rval,loc,c_op_loc,o_loc,c_loc,b_op_loc)
#define NEW_OP_ASGN2(r,t,i,o,val,loc,c_op_loc,m_loc,b_op_loc) (NODE *)rb_node_op_asgn2_new(p,r,val,i,o,t,loc,c_op_loc,m_loc,b_op_loc)
#define NEW_OP_ASGN_OR(i,val,loc) (NODE *)rb_node_op_asgn_or_new(p,i,val,loc)
#define NEW_OP_ASGN_AND(i,val,loc) (NODE *)rb_node_op_asgn_and_new(p,i,val,loc)
#define NEW_OP_CDECL(v,op,val,share,loc) (NODE *)rb_node_op_cdecl_new(p,v,val,op,share,loc)
#define NEW_CALL(r,m,a,loc) (NODE *)rb_node_call_new(p,r,m,a,loc)
#define NEW_OPCALL(r,m,a,loc) (NODE *)rb_node_opcall_new(p,r,m,a,loc)
#define NEW_FCALL(m,a,loc) rb_node_fcall_new(p,m,a,loc)
#define NEW_VCALL(m,loc) (NODE *)rb_node_vcall_new(p,m,loc)
#define NEW_QCALL0(r,m,a,loc) (NODE *)rb_node_qcall_new(p,r,m,a,loc)
#define NEW_SUPER(a,loc,k_loc,l_loc,r_loc) (NODE *)rb_node_super_new(p,a,loc,k_loc,l_loc,r_loc)
#define NEW_ZSUPER(loc) (NODE *)rb_node_zsuper_new(p,loc)
#define NEW_LIST(a,loc) (NODE *)rb_node_list_new(p,a,loc)
#define NEW_LIST2(h,l,n,loc) (NODE *)rb_node_list_new2(p,h,l,n,loc)
#define NEW_ZLIST(loc) (NODE *)rb_node_zlist_new(p,loc)
#define NEW_HASH(a,loc) (NODE *)rb_node_hash_new(p,a,loc)
#define NEW_RETURN(s,loc,k_loc) (NODE *)rb_node_return_new(p,s,loc,k_loc)
#define NEW_YIELD(a,loc,k_loc,l_loc,r_loc) (NODE *)rb_node_yield_new(p,a,loc,k_loc,l_loc,r_loc)
#define NEW_LVAR(v,loc) (NODE *)rb_node_lvar_new(p,v,loc)
#define NEW_DVAR(v,loc) (NODE *)rb_node_dvar_new(p,v,loc)
#define NEW_GVAR(v,loc) (NODE *)rb_node_gvar_new(p,v,loc)
#define NEW_IVAR(v,loc) (NODE *)rb_node_ivar_new(p,v,loc)
#define NEW_CONST(v,loc) (NODE *)rb_node_const_new(p,v,loc)
#define NEW_CVAR(v,loc) (NODE *)rb_node_cvar_new(p,v,loc)
#define NEW_NTH_REF(n,loc)  (NODE *)rb_node_nth_ref_new(p,n,loc)
#define NEW_BACK_REF(n,loc) (NODE *)rb_node_back_ref_new(p,n,loc)
#define NEW_MATCH2(n1,n2,loc) (NODE *)rb_node_match2_new(p,n1,n2,loc)
#define NEW_MATCH3(r,n2,loc) (NODE *)rb_node_match3_new(p,r,n2,loc)
#define NEW_INTEGER(val, base,loc) (NODE *)rb_node_integer_new(p,val,base,loc)
#define NEW_FLOAT(val,loc) (NODE *)rb_node_float_new(p,val,loc)
#define NEW_RATIONAL(val,base,seen_point,loc) (NODE *)rb_node_rational_new(p,val,base,seen_point,loc)
#define NEW_IMAGINARY(val,base,seen_point,numeric_type,loc) (NODE *)rb_node_imaginary_new(p,val,base,seen_point,numeric_type,loc)
#define NEW_STR(s,loc) (NODE *)rb_node_str_new(p,s,loc)
#define NEW_DSTR0(s,l,n,loc) (NODE *)rb_node_dstr_new0(p,s,l,n,loc)
#define NEW_DSTR(s,loc) (NODE *)rb_node_dstr_new(p,s,loc)
#define NEW_XSTR(s,loc) (NODE *)rb_node_xstr_new(p,s,loc)
#define NEW_DXSTR(s,l,n,loc) (NODE *)rb_node_dxstr_new(p,s,l,n,loc)
#define NEW_EVSTR(n,loc,o_loc,c_loc) (NODE *)rb_node_evstr_new(p,n,loc,o_loc,c_loc)
#define NEW_REGX(str,opts,loc,o_loc,ct_loc,c_loc) (NODE *)rb_node_regx_new(p,str,opts,loc,o_loc,ct_loc,c_loc)
#define NEW_ONCE(b,loc) (NODE *)rb_node_once_new(p,b,loc)
#define NEW_ARGS(loc) rb_node_args_new(p,loc)
#define NEW_ARGS_AUX(r,b,loc) rb_node_args_aux_new(p,r,b,loc)
#define NEW_OPT_ARG(v,loc) rb_node_opt_arg_new(p,v,loc)
#define NEW_KW_ARG(v,loc) rb_node_kw_arg_new(p,v,loc)
#define NEW_POSTARG(i,v,loc) (NODE *)rb_node_postarg_new(p,i,v,loc)
#define NEW_ARGSCAT(a,b,loc) (NODE *)rb_node_argscat_new(p,a,b,loc)
#define NEW_ARGSPUSH(a,b,loc) (NODE *)rb_node_argspush_new(p,a,b,loc)
#define NEW_SPLAT(a,loc,op_loc) (NODE *)rb_node_splat_new(p,a,loc,op_loc)
#define NEW_BLOCK_PASS(b,loc,o_loc) rb_node_block_pass_new(p,b,loc,o_loc)
#define NEW_DEFN(i,s,loc) (NODE *)rb_node_defn_new(p,i,s,loc)
#define NEW_DEFS(r,i,s,loc) (NODE *)rb_node_defs_new(p,r,i,s,loc)
#define NEW_ALIAS(n,o,loc,k_loc) (NODE *)rb_node_alias_new(p,n,o,loc,k_loc)
#define NEW_VALIAS(n,o,loc,k_loc,n_loc,o_loc) (NODE *)rb_node_valias_new(p,n,o,loc,k_loc,n_loc,o_loc)
#define NEW_UNDEF(i,loc) (NODE *)rb_node_undef_new(p,i,loc)
#define NEW_CLASS(n,b,s,loc,ck_loc,io_loc,ek_loc) (NODE *)rb_node_class_new(p,n,b,s,loc,ck_loc,io_loc,ek_loc)
#define NEW_MODULE(n,b,loc,mk_loc,ek_loc) (NODE *)rb_node_module_new(p,n,b,loc,mk_loc,ek_loc)
#define NEW_SCLASS(r,b,loc,ck_loc,op_loc,ek_loc) (NODE *)rb_node_sclass_new(p,r,b,loc,ck_loc,op_loc,ek_loc)
#define NEW_COLON2(c,i,loc,d_loc,n_loc) (NODE *)rb_node_colon2_new(p,c,i,loc,d_loc,n_loc)
#define NEW_COLON3(i,loc,d_loc,n_loc) (NODE *)rb_node_colon3_new(p,i,loc,d_loc,n_loc)
#define NEW_DOT2(b,e,loc,op_loc) (NODE *)rb_node_dot2_new(p,b,e,loc,op_loc)
#define NEW_DOT3(b,e,loc,op_loc) (NODE *)rb_node_dot3_new(p,b,e,loc,op_loc)
#define NEW_SELF(loc) (NODE *)rb_node_self_new(p,loc)
#define NEW_NIL(loc) (NODE *)rb_node_nil_new(p,loc)
#define NEW_TRUE(loc) (NODE *)rb_node_true_new(p,loc)
#define NEW_FALSE(loc) (NODE *)rb_node_false_new(p,loc)
#define NEW_ERRINFO(loc) (NODE *)rb_node_errinfo_new(p,loc)
#define NEW_DEFINED(e,loc,k_loc) (NODE *)rb_node_defined_new(p,e,loc, k_loc)
#define NEW_POSTEXE(b,loc,k_loc,o_loc,c_loc) (NODE *)rb_node_postexe_new(p,b,loc,k_loc,o_loc,c_loc)
#define NEW_SYM(str,loc) (NODE *)rb_node_sym_new(p,str,loc)
#define NEW_DSYM(s,l,n,loc) (NODE *)rb_node_dsym_new(p,s,l,n,loc)
#define NEW_ATTRASGN(r,m,a,loc) (NODE *)rb_node_attrasgn_new(p,r,m,a,loc)
#define NEW_LAMBDA(a,b,loc,op_loc,o_loc,c_loc) (NODE *)rb_node_lambda_new(p,a,b,loc,op_loc,o_loc,c_loc)
#define NEW_ARYPTN(pre,r,post,loc) (NODE *)rb_node_aryptn_new(p,pre,r,post,loc)
#define NEW_HSHPTN(c,kw,kwrest,loc) (NODE *)rb_node_hshptn_new(p,c,kw,kwrest,loc)
#define NEW_FNDPTN(pre,a,post,loc) (NODE *)rb_node_fndptn_new(p,pre,a,post,loc)
#define NEW_LINE(loc) (NODE *)rb_node_line_new(p,loc)
#define NEW_FILE(str,loc) (NODE *)rb_node_file_new(p,str,loc)
#define NEW_ENCODING(loc) (NODE *)rb_node_encoding_new(p,loc)
#define NEW_ERROR(loc) (NODE *)rb_node_error_new(p,loc)

enum internal_node_type {
    NODE_INTERNAL_ONLY = NODE_LAST,
    NODE_DEF_TEMP,
    NODE_EXITS,
    NODE_INTERNAL_LAST
};


/* This node is parse.y internal */
struct RNode_DEF_TEMP {
    NODE node;

    /* for NODE_DEFN/NODE_DEFS */

    NODE *nd_def;
    ID nd_mid;

    struct {
        int max_numparam;
        NODE *numparam_save;
        struct lex_context ctxt;
    } save;
};

#define RNODE_DEF_TEMP(node) ((struct RNode_DEF_TEMP *)(node))

static rb_node_break_t *rb_node_break_new(struct parser_params *p, NODE *nd_stts, const YYLTYPE *loc, const YYLTYPE *keyword_loc);
static rb_node_next_t *rb_node_next_new(struct parser_params *p, NODE *nd_stts, const YYLTYPE *loc, const YYLTYPE *keyword_loc);
static rb_node_redo_t *rb_node_redo_new(struct parser_params *p, const YYLTYPE *loc, const YYLTYPE *keyword_loc);
static rb_node_def_temp_t *rb_node_def_temp_new(struct parser_params *p, const YYLTYPE *loc);
static rb_node_def_temp_t *def_head_save(struct parser_params *p, rb_node_def_temp_t *n);

#define NEW_BREAK(s,loc,k_loc) (NODE *)rb_node_break_new(p,s,loc,k_loc)
#define NEW_NEXT(s,loc,k_loc) (NODE *)rb_node_next_new(p,s,loc,k_loc)
#define NEW_REDO(loc,k_loc) (NODE *)rb_node_redo_new(p,loc,k_loc)
#define NEW_DEF_TEMP(loc) rb_node_def_temp_new(p,loc)

/* Make a new internal node, which should not be appeared in the
 * result AST and does not have node_id and location. */
static NODE* node_new_internal(struct parser_params *p, enum node_type type, size_t size, size_t alignment);
#define NODE_NEW_INTERNAL(ndtype, type) (type *)node_new_internal(p, (enum node_type)(ndtype), sizeof(type), RUBY_ALIGNOF(type))

static NODE *nd_set_loc(NODE *nd, const YYLTYPE *loc);

static int
parser_get_node_id(struct parser_params *p)
{
    int node_id = p->node_id;
    p->node_id++;
    return node_id;
}

static void
anddot_multiple_assignment_check(struct parser_params* p, const YYLTYPE *loc, ID id)
{
    if (id == tANDDOT) {
        yyerror1(loc, "&. inside multiple assignment destination");
    }
}

static inline void
set_line_body(NODE *body, int line)
{
    /* linenos are not tracked; locations are byte offsets */
}

static void
set_embraced_location(NODE *node, const rb_code_location_t *beg, const rb_code_location_t *end)
{
    if (node != NULL && PM_NODE_TYPE_P(node, PM_BLOCK_NODE)) {
        pm_block_node_t *block = (pm_block_node_t *) node;
        block->opening_loc = pm_yloc(beg);
        block->closing_loc = pm_yloc(end);
        block->base.location = (pm_location_t) { beg->beg, end->end - beg->beg };
        if (block->body != NULL && PM_NODE_TYPE_P(block->body, PM_BEGIN_NODE)) {
            pm_ybegin_stamp_end(block->body, block->closing_loc);
            block->body->location = block->base.location;
        }
    }
}

static NODE *
last_expr_node(NODE *expr)
{
    return expr;
}

#define yyparse pm_yyparse

static NODE* cond(struct parser_params *p, NODE *node, const YYLTYPE *loc);
static NODE* method_cond(struct parser_params *p, NODE *node, const YYLTYPE *loc);
static NODE *new_nil_at(struct parser_params *p, const rb_code_position_t *pos);
static NODE *new_if(struct parser_params*,NODE*,NODE*,NODE*,const YYLTYPE*,const YYLTYPE*,const YYLTYPE*,const YYLTYPE*);
static NODE *new_unless(struct parser_params*,NODE*,NODE*,NODE*,const YYLTYPE*,const YYLTYPE*,const YYLTYPE*,const YYLTYPE*);
static NODE *logop(struct parser_params*,ID,NODE*,NODE*,const YYLTYPE*,const YYLTYPE*);

static NODE *newline_node(NODE*);
static void fixpos(NODE*,NODE*);

static int value_expr(struct parser_params*,NODE*);
static void void_expr(struct parser_params*,NODE*);
static NODE *remove_begin(NODE*);
static NODE *void_stmts(struct parser_params*,NODE*);
static void reduce_nodes(struct parser_params*,NODE**);
static void block_dup_check(struct parser_params*,NODE*,NODE*);

static NODE *block_append(struct parser_params*,NODE*,NODE*);
static NODE *list_append(struct parser_params*,NODE*,NODE*);
static NODE *list_concat(struct parser_params*,NODE*,NODE*);
static NODE *arg_append(struct parser_params*,NODE*,NODE*,const YYLTYPE*);
static NODE *last_arg_append(struct parser_params *p, NODE *args, NODE *last_arg, const YYLTYPE *loc);
static NODE *rest_arg_append(struct parser_params *p, NODE *args, NODE *rest_arg, const YYLTYPE *loc);
static NODE *literal_concat(struct parser_params*,NODE*,NODE*,const YYLTYPE*);
static NODE *new_evstr(struct parser_params*,NODE*,const YYLTYPE*,const YYLTYPE*,const YYLTYPE*);
static NODE *new_dstr(struct parser_params*,NODE*,const YYLTYPE*);
static NODE *str2dstr(struct parser_params*,NODE*);
static NODE *evstr2dstr(struct parser_params*,NODE*);
static NODE *splat_array(NODE*);
static void mark_lvar_used(struct parser_params *p, NODE *rhs);

static NODE *call_bin_op(struct parser_params*,NODE*,ID,NODE*,const YYLTYPE*,const YYLTYPE*);
static NODE *call_uni_op(struct parser_params*,NODE*,ID,const YYLTYPE*,const YYLTYPE*);
static NODE *new_qcall(struct parser_params* p, ID atype, NODE *recv, ID mid, NODE *args, const YYLTYPE *op_loc, const YYLTYPE *loc);
static NODE *new_command_qcall(struct parser_params* p, ID atype, NODE *recv, ID mid, NODE *args, NODE *block, const YYLTYPE *op_loc, const YYLTYPE *loc);
static NODE *method_add_block(struct parser_params*p, NODE *m, NODE *b, const YYLTYPE *loc)
{
    if (m != NULL && b != NULL && PM_NODE_TYPE_P(m, PM_CALL_NODE) && PM_NODE_TYPE_P(b, PM_BLOCK_NODE)) {
        ((pm_call_node_t *) m)->block = b;
        m->location = pm_yloc(loc);
    }
    else {
        YSTUB("method_add_block");
    }
    return m;
}
static NODE *command_add_block(struct parser_params*p, NODE *m, NODE *b, const YYLTYPE *loc);

static bool args_info_empty_p(struct rb_args_info *args);
static rb_node_args_t *new_args(struct parser_params*,rb_node_args_aux_t*,rb_node_opt_arg_t*,ID,rb_node_args_aux_t*,rb_node_args_t*,const YYLTYPE*);
static rb_node_args_t *new_args_tail(struct parser_params*,rb_node_kw_arg_t*,ID,ID,const YYLTYPE*);
#define new_empty_args_tail(p, loc) new_args_tail(p, 0, 0, 0, loc)
static NODE *new_array_pattern(struct parser_params *p, NODE *constant, NODE *pre_arg, NODE *aryptn, const YYLTYPE *loc);
static NODE *new_array_pattern_tail(struct parser_params *p, NODE *pre_args, int has_rest, NODE *rest_arg, NODE *post_args, const YYLTYPE *loc);
static NODE *new_find_pattern(struct parser_params *p, NODE *constant, NODE *fndptn, const YYLTYPE *loc);
static NODE *new_find_pattern_tail(struct parser_params *p, NODE *pre_rest_arg, NODE *args, NODE *post_rest_arg, const YYLTYPE *loc);
static NODE *new_hash_pattern(struct parser_params *p, NODE *constant, NODE *hshptn, const YYLTYPE *loc);
static NODE *new_hash_pattern_tail(struct parser_params *p, NODE *kw_args, ID kw_rest_arg, const YYLTYPE *loc);

static rb_node_kw_arg_t *new_kw_arg(struct parser_params *p, NODE *k, const YYLTYPE *loc);
static rb_node_args_t *args_with_numbered(struct parser_params*,rb_node_args_t*,int,ID);

static NODE* negate_lit(struct parser_params*, NODE*,const YYLTYPE*);
static void no_blockarg(struct parser_params*,NODE*);
static NODE *ret_args(struct parser_params*,NODE*);
static NODE *arg_blk_pass(struct parser_params*,NODE*,rb_node_block_pass_t*);
static NODE *dsym_node(struct parser_params*,NODE*,const YYLTYPE*);

static NODE *gettable(struct parser_params*,ID,const YYLTYPE*);
static NODE *assignable(struct parser_params*,ID,NODE*,const YYLTYPE*);

static NODE *aryset(struct parser_params*,NODE*,NODE*,const YYLTYPE*);
static NODE *attrset(struct parser_params*,NODE*,ID,ID,const YYLTYPE*);

static VALUE rb_backref_error(struct parser_params*,NODE*);
static NODE *node_assign(struct parser_params*,NODE*,NODE*,struct lex_context,const YYLTYPE*);

static NODE *new_op_assign(struct parser_params *p, NODE *lhs, ID op, NODE *rhs, struct lex_context, const YYLTYPE *op_loc, const YYLTYPE *loc);
static NODE *new_ary_op_assign(struct parser_params *p, NODE *ary, NODE *args, ID op, NODE *rhs, const YYLTYPE *args_loc, const YYLTYPE *loc, const YYLTYPE *call_operator_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc, const YYLTYPE *binary_operator_loc);
static NODE *new_attr_op_assign(struct parser_params *p, NODE *lhs, ID atype, ID attr, ID op, NODE *rhs, const YYLTYPE *loc, const YYLTYPE *call_operator_loc, const YYLTYPE *message_loc, const YYLTYPE *binary_operator_loc);
static NODE *new_const_op_assign(struct parser_params *p, NODE *lhs, ID op, NODE *rhs, struct lex_context, const YYLTYPE *loc);
static NODE *new_bodystmt(struct parser_params *p, NODE *head, NODE *rescue, NODE *rescue_else, NODE *ensure, const YYLTYPE *loc);

static NODE *const_decl(struct parser_params *p, NODE* path, const YYLTYPE *loc);

static rb_node_opt_arg_t *opt_arg_append(struct parser_params*, rb_node_opt_arg_t*, rb_node_opt_arg_t*);
static rb_node_kw_arg_t *kwd_append(struct parser_params*, rb_node_kw_arg_t*, rb_node_kw_arg_t*);

static NODE *new_hash(struct parser_params *p, NODE *hash, const YYLTYPE *loc);
static NODE *new_unique_key_hash(struct parser_params *p, NODE *hash, const YYLTYPE *loc);

static NODE *new_defined(struct parser_params *p, NODE *expr, const YYLTYPE *loc, const YYLTYPE *keyword_loc);

static NODE *new_regexp(struct parser_params *, NODE *, int, const YYLTYPE *, const YYLTYPE *, const YYLTYPE *, const YYLTYPE *);

#define make_list(list, loc) ((list) ? (((NODE *)(list))->location = pm_yloc(loc), (list)) : NEW_ZLIST(loc))

static NODE *new_xstring(struct parser_params *, NODE *, const YYLTYPE *loc);

static NODE *symbol_append(struct parser_params *p, NODE *symbols, NODE *symbol);

static NODE *match_op(struct parser_params*,NODE*,NODE*,const YYLTYPE*,const YYLTYPE*);

static rb_ast_id_table_t *local_tbl(struct parser_params*);

static VALUE reg_compile(struct parser_params*, rb_parser_string_t*, int);
static void reg_fragment_setenc(struct parser_params*, rb_parser_string_t*, int);

static int literal_concat0(struct parser_params *p, rb_parser_string_t *head, rb_parser_string_t *tail);
static NODE *heredoc_dedent(struct parser_params*,NODE*);

static void check_literal_when(struct parser_params *p, NODE *args, const YYLTYPE *loc);

static rb_locations_lambda_body_t* new_locations_lambda_body(struct parser_params *p, NODE *node, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc);


static int rb_reg_fragment_setenc(struct parser_params*, rb_parser_string_t *, int);
static int rb_parser_search_nonascii2(const char *ptr, long len);

static void flush_string_content(struct parser_params *p, rb_encoding *enc, size_t back);
static void error_duplicate_pattern_variable(struct parser_params *p, ID id, const YYLTYPE *loc);
static void error_duplicate_pattern_key(struct parser_params *p, ID id, const YYLTYPE *loc);
static VALUE formal_argument_error(struct parser_params*, ID);
static ID shadowing_lvar(struct parser_params*,ID);
static void new_bv(struct parser_params*,ID);

static void local_push(struct parser_params*,int);
static void local_pop(struct parser_params*);
static void local_var(struct parser_params*, ID);
static void arg_var(struct parser_params*, ID);
static int  local_id(struct parser_params *p, ID id);
static int  local_id_ref(struct parser_params*, ID, ID **);
#define internal_id rb_parser_internal_id
static ID internal_id(struct parser_params*);
static NODE *new_args_forward_call(struct parser_params*, NODE*, const YYLTYPE*, const YYLTYPE*);
static int check_forwarding_args(struct parser_params*);
static void add_forwarding_args(struct parser_params *p);
static void forwarding_arg_check(struct parser_params *p, ID arg, ID all, const char *var);

static const struct vtable *dyna_push(struct parser_params *);
static void dyna_pop(struct parser_params*, const struct vtable *);
static int dyna_in_block(struct parser_params*);
#define dyna_var(p, id) local_var(p, id)
static int dvar_defined(struct parser_params*, ID);
#define dvar_defined_ref rb_parser_dvar_defined_ref
static int dvar_defined_ref(struct parser_params*, ID, ID**);
static int dvar_curr(struct parser_params*,ID);

static int lvar_defined(struct parser_params*, ID);

static NODE *numparam_push(struct parser_params *p);
static void numparam_pop(struct parser_params *p, NODE *prev_inner);

#define METHOD_NOT '!'

#define idFWD_REST   '*'
#define idFWD_KWREST idPow /* Use simple "**", as tDSTAR is "**arg" */
#define idFWD_BLOCK  '&'
#define idFWD_ALL    idDot3
#define arg_FWD_BLOCK idFWD_BLOCK

#define RE_ONIG_OPTION_IGNORECASE 1
#define RE_ONIG_OPTION_EXTEND     (RE_ONIG_OPTION_IGNORECASE<<1)
#define RE_ONIG_OPTION_MULTILINE  (RE_ONIG_OPTION_EXTEND<<1)
#define RE_OPTION_ONCE (1<<16)
#define RE_OPTION_ENCODING_SHIFT 8
#define RE_OPTION_ENCODING(e) (((e)&0xff)<<RE_OPTION_ENCODING_SHIFT)
#define RE_OPTION_ENCODING_IDX(o) (((o)>>RE_OPTION_ENCODING_SHIFT)&0xff)
#define RE_OPTION_ENCODING_NONE(o) ((o)&RE_OPTION_ARG_ENCODING_NONE)
#define RE_OPTION_MASK  0xff
#define RE_OPTION_ARG_ENCODING_NONE 32

#define CHECK_LITERAL_WHEN (st_table *)1
#define CASE_LABELS_ENABLED_P(case_labels) (case_labels && case_labels != CHECK_LITERAL_WHEN)

#define yytnamerr(yyres, yystr) (YYSIZE_T)rb_yytnamerr(p, yyres, yystr)
RUBY_FUNC_EXPORTED size_t rb_yytnamerr(struct parser_params *p, char *yyres, const char *yystr);

#define TOKEN2ID(tok) ( \
    tTOKEN_LOCAL_BEGIN<(tok)&&(tok)<tTOKEN_LOCAL_END ? TOKEN2LOCALID(tok) : \
    tTOKEN_INSTANCE_BEGIN<(tok)&&(tok)<tTOKEN_INSTANCE_END ? TOKEN2INSTANCEID(tok) : \
    tTOKEN_GLOBAL_BEGIN<(tok)&&(tok)<tTOKEN_GLOBAL_END ? TOKEN2GLOBALID(tok) : \
    tTOKEN_CONST_BEGIN<(tok)&&(tok)<tTOKEN_CONST_END ? TOKEN2CONSTID(tok) : \
    tTOKEN_CLASS_BEGIN<(tok)&&(tok)<tTOKEN_CLASS_END ? TOKEN2CLASSID(tok) : \
    tTOKEN_ATTRSET_BEGIN<(tok)&&(tok)<tTOKEN_ATTRSET_END ? TOKEN2ATTRSETID(tok) : \
    ((tok) / ((tok)<tPRESERVED_ID_END && ((tok)>=128 || rb_ispunct(tok)))))

/****** Ripper *******/


#define KWD2EID(t, v) keyword_##t

static NODE *
new_scope_body(struct parser_params *p, rb_node_args_t *args, NODE *body, NODE *parent, const YYLTYPE *loc)
{
    body = remove_begin(body);
    reduce_nodes(p, &body);
    NODE *n = NEW_SCOPE(args, body, parent, loc);
    nd_set_line(n, loc->end_pos.lineno);
    return n;
}

static NODE *
rescued_expr(struct parser_params *p, NODE *arg, NODE *rescue,
             const YYLTYPE *arg_loc, const YYLTYPE *mod_loc, const YYLTYPE *res_loc)
{
    YYLTYPE loc = { arg_loc->beg, res_loc->end };
    return pm_yrescue_modifier(p, arg, remove_begin(rescue), mod_loc, &loc);
}

static NODE *add_block_exit(struct parser_params *p, NODE *node);
static rb_node_exits_t *init_block_exit(struct parser_params *p);
static rb_node_exits_t *allow_block_exit(struct parser_params *p);
static void restore_block_exit(struct parser_params *p, rb_node_exits_t *exits);
static void clear_block_exit(struct parser_params *p, bool error);

static void
next_rescue_context(struct lex_context *next, const struct lex_context *outer, enum rescue_context def)
{
    next->in_rescue = outer->in_rescue == after_rescue ? after_rescue : def;
}

static void
restore_defun(struct parser_params *p, rb_node_def_temp_t *temp)
{
    /* See: def_name action */
    struct lex_context ctxt = temp->save.ctxt;
    p->ctxt.in_def = ctxt.in_def;
    p->ctxt.shareable_constant_value = ctxt.shareable_constant_value;
    p->ctxt.in_rescue = ctxt.in_rescue;
    p->max_numparam = temp->save.max_numparam;
    numparam_pop(p, temp->save.numparam_save);
    clear_block_exit(p, true);
}

static void
endless_method_name(struct parser_params *p, ID mid, const YYLTYPE *loc)
{
    if (is_attrset_id(mid)) {
        yyerror1(loc, "setter method cannot be defined in an endless method definition");
    }
}

#define debug_token_line(p, name, line) do { \
        if (p->debug) { \
            const char *const pcur = p->lex.pcur; \
            const char *const ptok = p->lex.ptok; \
            rb_parser_printf(p, name ":%d (%d: %"PRIdPTRDIFF"|%"PRIdPTRDIFF"|%"PRIdPTRDIFF")\n", \
                             line, p->ruby_sourceline, \
                             ptok - p->lex.pbeg, pcur - ptok, p->lex.pend - pcur); \
        } \
    } while (0)

#define begin_definition(k, loc_beg, loc_end) \
    do { \
        if (!(p->ctxt.in_class = (k)[0] != 0)) { \
            /* singleton class */ \
            p->ctxt.cant_return = !p->ctxt.in_def; \
            p->ctxt.in_def = 0; \
        } \
        else if (p->ctxt.in_def) { \
            YYLTYPE loc = code_loc_gen(loc_beg, loc_end); \
            yyerror1(&loc, k " definition in method body"); \
        } \
        else { \
            p->ctxt.cant_return = 1; \
        } \
        local_push(p, 0); \
    } while (0)

# define ifndef_ripper(x) (x)
# define ifdef_ripper(r,x) (x)

# define rb_warn0(fmt) ((void) 0)
# define rb_warn1(fmt,a) ((void) (a))
# define rb_warn2(fmt,a,b) ((void) (a), (void) (b))
# define rb_warn3(fmt,a,b,c) ((void) (a), (void) (b), (void) (c))
# define rb_warn4(fmt,a,b,c,d) ((void) (a), (void) (b), (void) (c), (void) (d))
# define rb_warning0(fmt) ((void) 0)
# define rb_warning1(fmt,a) ((void) (a))
# define rb_warning2(fmt,a,b) ((void) (a), (void) (b))
# define rb_warning3(fmt,a,b,c) ((void) (a), (void) (b), (void) (c))
# define rb_warning4(fmt,a,b,c,d) ((void) (a), (void) (b), (void) (c), (void) (d))
# define rb_warn0L(l,fmt) ((void) (l))
# define rb_warn1L(l,fmt,a) ((void) (l), (void) (a))
# define rb_warn2L(l,fmt,a,b) ((void) (l), (void) (a), (void) (b))
# define rb_warn3L(l,fmt,a,b,c) ((void) (l), (void) (a), (void) (b), (void) (c))
# define rb_warn4L(l,fmt,a,b,c,d) ((void) (l), (void) (a), (void) (b), (void) (c), (void) (d))
# define rb_warning0L(l,fmt) ((void) (l))
# define rb_warning1L(l,fmt,a) ((void) (l), (void) (a))
# define rb_warning2L(l,fmt,a,b) ((void) (l), (void) (a), (void) (b))
# define rb_warning3L(l,fmt,a,b,c) ((void) (l), (void) (a), (void) (b), (void) (c))
# define rb_warning4L(l,fmt,a,b,c,d) ((void) (l), (void) (a), (void) (b), (void) (c), (void) (d))
# define WARN_S_L(s,l) s
# define WARN_S(s) s
# define WARN_I(i) i
# define WARN_ID(i) (i)
# define PRIsWARN "s"

PRINTF_ARGS(static void parser_compile_error(struct parser_params*, const rb_code_location_t *loc, const char *fmt, ...), 3, 4);
# define compile_error(p, ...) parser_compile_error(p, NULL, __VA_ARGS__)

#define RNODE_EXITS(node) ((rb_node_exits_t*)(node))

static NODE *
add_block_exit(struct parser_params *p, NODE *node)
{
    return node;
}

static rb_node_exits_t *
init_block_exit(struct parser_params *p)
{
    /* block exit validation is not ported */
    return NULL;
}

static rb_node_exits_t *
allow_block_exit(struct parser_params *p)
{
    return NULL;
}

static void
restore_block_exit(struct parser_params *p, rb_node_exits_t *exits)
{
    /* block exit validation is not ported */
}

static void
clear_block_exit(struct parser_params *p, bool error)
{
    /* block exit validation is not ported */
}

#define WARN_EOL(tok) \
    (looking_at_eol_p(p) ? \
     (void)rb_warning0("'" tok "' at the end of line without an expression") : \
     (void)0)
static int looking_at_eol_p(struct parser_params *p);

static NODE *
get_nd_value(struct parser_params *p, NODE *node)
{
    switch (PM_NODE_TYPE(node)) {
      case PM_LOCAL_VARIABLE_WRITE_NODE: return ((pm_local_variable_write_node_t *) node)->value;
      case PM_GLOBAL_VARIABLE_WRITE_NODE: return ((pm_global_variable_write_node_t *) node)->value;
      case PM_INSTANCE_VARIABLE_WRITE_NODE: return ((pm_instance_variable_write_node_t *) node)->value;
      case PM_CLASS_VARIABLE_WRITE_NODE: return ((pm_class_variable_write_node_t *) node)->value;
      case PM_CONSTANT_WRITE_NODE: return ((pm_constant_write_node_t *) node)->value;
      default:
        YSTUB("get_nd_value");
        return NULL;
    }
}

static void
set_nd_value(struct parser_params *p, NODE *node, NODE *rhs)
{
    switch (PM_NODE_TYPE(node)) {
      case PM_LOCAL_VARIABLE_WRITE_NODE: ((pm_local_variable_write_node_t *) node)->value = rhs; break;
      case PM_GLOBAL_VARIABLE_WRITE_NODE: ((pm_global_variable_write_node_t *) node)->value = rhs; break;
      case PM_INSTANCE_VARIABLE_WRITE_NODE: ((pm_instance_variable_write_node_t *) node)->value = rhs; break;
      case PM_CLASS_VARIABLE_WRITE_NODE: ((pm_class_variable_write_node_t *) node)->value = rhs; break;
      case PM_CONSTANT_WRITE_NODE: ((pm_constant_write_node_t *) node)->value = rhs; break;
      case PM_CONSTANT_PATH_WRITE_NODE: ((pm_constant_path_write_node_t *) node)->value = rhs; break;
      default:
        YSTUB("set_nd_value");
        break;
    }
}

static ID
get_nd_vid(struct parser_params *p, NODE *node)
{
    YSTUB("get_nd_vid");
    return 0;
}

static NODE *
get_nd_args(struct parser_params *p, NODE *node)
{
    /* PORTME: returns the call's arguments once block-pass is ported */
    return NULL;
}

static st_index_t
djb2(const uint8_t *str, size_t len)
{
    st_index_t hash = 5381;

    for (size_t i = 0; i < len; i++) {
        hash = ((hash << 5) + hash) + str[i];
    }

    return hash;
}

static st_index_t
parser_memhash(const void *ptr, long len)
{
    return djb2(ptr, len);
}

#define PARSER_STRING_PTR(str) (str->ptr)
#define PARSER_STRING_LEN(str) (str->len)
#define PARSER_STRING_END(str) (&str->ptr[str->len])
#define STRING_SIZE(str) ((size_t)str->len + 1)
#define STRING_TERM_LEN(str) (1)
#define STRING_TERM_FILL(str) (str->ptr[str->len] = '\0')
#define PARSER_STRING_RESIZE_CAPA_TERM(p,str,capacity,termlen) do {\
    REALLOC_N(str->ptr, char, (size_t)total + termlen); \
    str->len = total; \
} while (0)
#define STRING_SET_LEN(str, n) do { \
    (str)->len = (n); \
} while (0)
#define PARSER_STRING_GETMEM(str, ptrvar, lenvar) \
    ((ptrvar) = str->ptr,                            \
     (lenvar) = str->len)

static inline int
parser_string_char_at_end(struct parser_params *p, rb_parser_string_t *str, int when_empty)
{
    return PARSER_STRING_LEN(str) > 0 ? (unsigned char)PARSER_STRING_END(str)[-1] : when_empty;
}

/*
 * CRuby's parser-string layer, mapped onto ystring. The functions this
 * replaces are in CRuby's parse.y around rb_parser_string_new; each mapping
 * notes any signature difference it papers over (usually the leading parser
 * argument, which ystring does not need).
 */
#define rb_parser_string_new(p, ptr, len) pm_ystring_new((ptr), (long) (len), NULL)
#define rb_parser_encoding_string_new(p, ptr, len, enc) pm_ystring_new((ptr), (long) (len), (enc))
#define rb_parser_string_free(p, str) pm_ystring_free(str)
#define rb_parser_str_hash(str) ((st_index_t) pm_ystring_hash(str))
#define rb_parser_string_end(str) PM_YSTRING_END(str)
#define rb_parser_string_set_encoding(str, enc) pm_ystring_set_encoding((str), (enc))
#define rb_parser_str_get_encoding(str) ((str)->enc)
#define PARSER_ENCODING_IS_ASCII8BIT(p, str) ((str)->enc == rb_ascii8bit_encoding())
#define PARSER_ENC_CODERANGE(str) ((int) (str)->coderange)
#define PARSER_ENC_CODERANGE_SET(str, cr) ((str)->coderange = (pm_ystring_coderange_t) (cr))
#define PARSER_ENC_CODERANGE_CLEAR(str) ((str)->coderange = PM_YSTRING_CODERANGE_UNKNOWN)
#define PARSER_ENCODING_CODERANGE_SET(str, enc, cr) (pm_ystring_set_encoding((str), (enc)), PARSER_ENC_CODERANGE_SET((str), (cr)))
#define PARSER_ENC_CODERANGE_ASCIIONLY(str) ((str)->coderange == PM_YSTRING_CODERANGE_7BIT)
#define PARSER_ENC_CODERANGE_CLEAN_P(cr) ((cr) == RB_PARSER_ENC_CODERANGE_7BIT || (cr) == RB_PARSER_ENC_CODERANGE_VALID)
#define RB_PARSER_ENC_CODERANGE_UNKNOWN PM_YSTRING_CODERANGE_UNKNOWN
#define RB_PARSER_ENC_CODERANGE_7BIT PM_YSTRING_CODERANGE_7BIT
#define RB_PARSER_ENC_CODERANGE_VALID PM_YSTRING_CODERANGE_VALID
#define RB_PARSER_ENC_CODERANGE_BROKEN PM_YSTRING_CODERANGE_BROKEN
#define rb_parser_coderange_scan(p, ptr, len, enc) ((int) pm_ystring_coderange_scan((ptr), (len), (enc)))
#define rb_parser_enc_coderange_scan(p, str, enc) ((int) pm_ystring_coderange_scan((str)->ptr, (str)->len, (enc)))
#define rb_parser_enc_str_coderange(p, str) ((int) pm_ystring_coderange(str))
#define rb_parser_enc_associate(p, str, enc) pm_ystring_associate_encoding((str), (enc))
#define rb_parser_is_ascii_string(p, str) pm_ystring_ascii_only_p(str)
#define rb_parser_enc_compatible(p, str1, str2) pm_ystring_compatible_encoding((str1), (str2))
#define rb_parser_str_modify(str) pm_ystring_modify(str)
#define rb_parser_str_set_len(p, str, len) pm_ystring_set_len((str), (len))
#define rb_parser_str_buf_cat(p, str, ptr, len) (pm_ystring_cat((str), (ptr), (len)), (str))
#define rb_parser_str_buf_append(p, str, str2) (pm_ystring_append((str), (str2)), (str))
#define rb_parser_str_resize(p, str, len) (pm_ystring_resize((str), (len)), (str))
/* strcmp-shaped: zero when equal. */
#define rb_parser_string_hash_cmp(str1, str2) (!pm_ystring_equal((str1), (str2)))

/*
 * Concatenate bytes in a given encoding onto a string, reconciling the
 * encodings and coderanges. CRuby's version threads Onigmo coderange scans
 * through the append; this one appends and lets the coderange be rescanned
 * lazily, which is the same observable behavior at the cost of a rescan.
 */
static rb_parser_string_t *
rb_parser_enc_cr_str_buf_cat(struct parser_params *p, rb_parser_string_t *str, const char *ptr, long len,
    rb_encoding *ptr_enc, int ptr_cr, int *ptr_cr_ret)
{
    rb_encoding *str_enc = str->enc;

    if (str_enc != ptr_enc && str->len > 0 && !pm_ystring_ascii_only_p(str)) {
        /* Both sides have bytes that only mean something in their own
         * encodings; CRuby raises here. Record it and keep the string's own
         * encoding so the parse can continue. */
        pm_ystring_coderange_t cr = pm_ystring_coderange_scan(ptr, len, ptr_enc);
        if (cr != PM_YSTRING_CODERANGE_7BIT) {
            yyerror0("string concatenation of incompatible encodings");
        }
    }

    pm_ystring_cat(str, ptr, len);
    if (str_enc != ptr_enc && pm_ystring_coderange_scan(ptr, len, ptr_enc) != PM_YSTRING_CODERANGE_7BIT) {
        pm_ystring_set_encoding(str, ptr_enc);
    }

    if (ptr_cr_ret) *ptr_cr_ret = (int) pm_ystring_coderange_scan(ptr, len, ptr_enc);
    return str;
}

static rb_parser_string_t *
rb_parser_enc_str_buf_cat(struct parser_params *p, rb_parser_string_t *str, const char *ptr, long len,
    rb_encoding *ptr_enc)
{
    return rb_parser_enc_cr_str_buf_cat(p, str, ptr, len, ptr_enc, -1, NULL);
}

%}

%expect 0
%define api.pure
%define parse.error verbose


%lex-param {struct parser_params *p}
%parse-param {struct parser_params *p}
%initial-action
{
    RUBY_SET_YYLLOC_OF_NONE(@$);
};

%union {
    NODE *node;
    rb_node_fcall_t *node_fcall;
    rb_node_args_t *node_args;
    rb_node_args_aux_t *node_args_aux;
    rb_node_opt_arg_t *node_opt_arg;
    rb_node_kw_arg_t *node_kw_arg;
    rb_node_block_pass_t *node_block_pass;
    rb_node_masgn_t *node_masgn;
    rb_node_def_temp_t *node_def_temp;
    rb_node_exits_t *node_exits;
    struct rb_locations_lambda_body_t *locations_lambda_body;
    ID id;
    int num;
    st_table *tbl;
    st_table *labels;
    const struct vtable *vars;
    struct rb_strterm_struct *strterm;
    struct lex_context ctxt;
    enum lex_state_e state;
}

%token <id>
        keyword_class        "'class'"
        keyword_module       "'module'"
        keyword_def          "'def'"
        keyword_undef        "'undef'"
        keyword_begin        "'begin'"
        keyword_rescue       "'rescue'"
        keyword_ensure       "'ensure'"
        keyword_end          "'end'"
        keyword_if           "'if'"
        keyword_unless       "'unless'"
        keyword_then         "'then'"
        keyword_elsif        "'elsif'"
        keyword_else         "'else'"
        keyword_case         "'case'"
        keyword_when         "'when'"
        keyword_while        "'while'"
        keyword_until        "'until'"
        keyword_for          "'for'"
        keyword_break        "'break'"
        keyword_next         "'next'"
        keyword_redo         "'redo'"
        keyword_retry        "'retry'"
        keyword_in           "'in'"
        keyword_do           "'do'"
        keyword_do_cond      "'do' for condition"
        keyword_do_block     "'do' for block"
        keyword_do_LAMBDA    "'do' for lambda"
        keyword_return       "'return'"
        keyword_yield        "'yield'"
        keyword_super        "'super'"
        keyword_self         "'self'"
        keyword_nil          "'nil'"
        keyword_true         "'true'"
        keyword_false        "'false'"
        keyword_and          "'and'"
        keyword_or           "'or'"
        keyword_not          "'not'"
        modifier_if          "'if' modifier"
        modifier_unless      "'unless' modifier"
        modifier_while       "'while' modifier"
        modifier_until       "'until' modifier"
        modifier_rescue      "'rescue' modifier"
        keyword_alias        "'alias'"
        keyword_defined      "'defined?'"
        keyword_BEGIN        "'BEGIN'"
        keyword_END          "'END'"
        keyword__LINE__      "'__LINE__'"
        keyword__FILE__      "'__FILE__'"
        keyword__ENCODING__  "'__ENCODING__'"

%token <id>   tIDENTIFIER    "local variable or method"
%token <id>   tFID           "method"
%token <id>   tGVAR          "global variable"
%token <id>   tIVAR          "instance variable"
%token <id>   tCONSTANT      "constant"
%token <id>   tCVAR          "class variable"
%token <id>   tLABEL         "label"
%token <node> tINTEGER       "integer literal"
%token <node> tFLOAT         "float literal"
%token <node> tRATIONAL      "rational literal"
%token <node> tIMAGINARY     "imaginary literal"
%token <node> tCHAR          "char literal"
%token <node> tNTH_REF       "numbered reference"
%token <node> tBACK_REF      "back reference"
%token <node> tSTRING_CONTENT "literal content"
%token <num>  tREGEXP_END
%token <num>  tDUMNY_END     "dummy end"

%type <node> singleton singleton_expr strings string string1 xstring regexp
%type <node> string_contents xstring_contents regexp_contents string_content
%type <node> words symbols symbol_list qwords qsymbols word_list qword_list qsym_list word
%type <node> literal numeric simple_numeric ssym dsym symbol cpath
%type <node_def_temp> defn_head defs_head k_def
%type <node_exits> block_open k_while k_until k_for allow_exits
%type <node> top_stmts top_stmt begin_block endless_arg endless_command
%type <node> bodystmt stmts stmt_or_begin stmt expr arg ternary primary
%type <node> command command_call command_call_value method_call
%type <node> expr_value expr_value_do arg_value primary_value rel_expr
%type <node_fcall> fcall
%type <node> if_tail opt_else case_body case_args cases opt_rescue exc_list exc_var opt_ensure
%type <node> args arg_splat call_args opt_call_args
%type <node> paren_args opt_paren_args
%type <node_args> args_tail block_args_tail
%type <node> command_args aref_args
%type <node_block_pass> opt_block_arg block_arg
%type <node> var_ref var_lhs
%type <node> command_rhs arg_rhs
%type <node> command_asgn mrhs mrhs_arg superclass block_call block_command
%type <node_args> f_arglist f_opt_paren_args f_paren_args f_args f_empty_arg
%type <node_args_aux> f_arg f_arg_item
%type <node> f_marg f_rest_marg
%type <node_masgn> f_margs
%type <node> assoc_list assocs assoc undef_list backref string_dvar for_var
%type <node_args> block_param opt_block_param_def block_param_def opt_block_param
%type <id> do bv_decls opt_bv_decl bvar
%type <node> lambda brace_body do_body
%type <locations_lambda_body> lambda_body
%type <node_args> f_larglist f_largs largs_tail
%type <node> brace_block cmd_brace_block do_block lhs none fitem
%type <node> mlhs_head mlhs_item mlhs_node
%type <node_masgn> mlhs mlhs_basic mlhs_inner
%type <node> p_case_body p_cases p_top_expr p_top_expr_body
%type <node> p_expr p_as p_alt p_expr_basic p_find
%type <node> p_args p_args_head p_args_tail p_args_post p_arg p_rest
%type <node> p_value p_primitive p_variable p_var_ref p_expr_ref p_const
%type <node> p_kwargs p_kwarg p_kw
%type <id>   keyword_variable user_variable sym operation2 operation3
%type <id>   cname fname op f_rest_arg f_block_arg opt_comma f_norm_arg f_bad_arg
%type <id>   f_kwrest f_label f_arg_asgn call_op call_op2 reswords relop dot_or_colon
%type <id>   p_kwrest p_kwnorest p_any_kwrest p_kw_label
%type <id>   f_no_kwarg f_any_kwrest args_forward excessed_comma nonlocal_var def_name
%type <ctxt> lex_ctxt begin_defined k_class k_module k_END k_rescue k_ensure after_rescue
%type <ctxt> p_in_kwarg
%type <tbl>  p_lparen p_lbracket p_pktbl p_pvtbl
%type <num>  max_numparam
%type <node> numparam
%type <id>   it_id
%token END_OF_INPUT 0	"end-of-input"
%token <id> '.'

/* escaped chars, should be ignored otherwise */
%token <id> '\\'	"backslash"
%token tSP		"escaped space"
%token <id> '\t' 	"escaped horizontal tab"
%token <id> '\f'	"escaped form feed"
%token <id> '\r'	"escaped carriage return"
%token <id> '\13'	"escaped vertical tab"
%token tUPLUS		RUBY_TOKEN(UPLUS)  "unary+"
%token tUMINUS		RUBY_TOKEN(UMINUS) "unary-"
%token tPOW		RUBY_TOKEN(POW)    "**"
%token tCMP		RUBY_TOKEN(CMP)    "<=>"
%token tEQ		RUBY_TOKEN(EQ)     "=="
%token tEQQ		RUBY_TOKEN(EQQ)    "==="
%token tNEQ		RUBY_TOKEN(NEQ)    "!="
%token tGEQ		RUBY_TOKEN(GEQ)    ">="
%token tLEQ		RUBY_TOKEN(LEQ)    "<="
%token tANDOP		RUBY_TOKEN(ANDOP)  "&&"
%token tOROP		RUBY_TOKEN(OROP)   "||"
%token tMATCH		RUBY_TOKEN(MATCH)  "=~"
%token tNMATCH		RUBY_TOKEN(NMATCH) "!~"
%token tDOT2		RUBY_TOKEN(DOT2)   ".."
%token tDOT3		RUBY_TOKEN(DOT3)   "..."
%token tBDOT2		RUBY_TOKEN(BDOT2)   "(.."
%token tBDOT3		RUBY_TOKEN(BDOT3)   "(..."
%token tAREF		RUBY_TOKEN(AREF)   "[]"
%token tASET		RUBY_TOKEN(ASET)   "[]="
%token tLSHFT		RUBY_TOKEN(LSHFT)  "<<"
%token tRSHFT		RUBY_TOKEN(RSHFT)  ">>"
%token <id> tANDDOT	RUBY_TOKEN(ANDDOT) "&."
%token <id> tCOLON2	RUBY_TOKEN(COLON2) "::"
%token tCOLON3		":: at EXPR_BEG"
%token <id> tOP_ASGN	"operator-assignment" /* +=, -=  etc. */
%token tASSOC		"=>"
%token tLPAREN		"("
%token tLPAREN_ARG	"( arg"
%token tLBRACK		"["
%token tLBRACE		"{"
%token tLBRACE_ARG	"{ arg"
%token tSTAR		"*"
%token tDSTAR		"**arg"
%token tAMPER		"&"
%token <num> tLAMBDA	"->"
%token tSYMBEG		"symbol literal"
%token tSTRING_BEG	"string literal"
%token tXSTRING_BEG	"backtick literal"
%token tREGEXP_BEG	"regexp literal"
%token tWORDS_BEG	"word list"
%token tQWORDS_BEG	"verbatim word list"
%token tSYMBOLS_BEG	"symbol list"
%token tQSYMBOLS_BEG	"verbatim symbol list"
%token tSTRING_END	"terminator"
%token tSTRING_DEND	"'}'"
%token <state> tSTRING_DBEG "'#{'"
%token tSTRING_DVAR tLAMBEG tLABEL_END

%token tIGNORED_NL tCOMMENT tEMBDOC_BEG tEMBDOC tEMBDOC_END
%token tHEREDOC_BEG tHEREDOC_END k__END__

/*
 *	precedence table
 */

%nonassoc tLOWEST
%nonassoc tLBRACE_ARG

%nonassoc  modifier_if modifier_unless modifier_while modifier_until keyword_in
%left  keyword_or keyword_and
%right keyword_not
%nonassoc keyword_defined
%right '=' tOP_ASGN
%left modifier_rescue
%right '?' ':'
%nonassoc tDOT2 tDOT3 tBDOT2 tBDOT3
%left  tOROP
%left  tANDOP
%nonassoc  tCMP tEQ tEQQ tNEQ tMATCH tNMATCH
%left  '>' tGEQ '<' tLEQ
%left  '|' '^'
%left  '&'
%left  tLSHFT tRSHFT
%left  '+' '-'
%left  '*' '/' '%'
%right tUMINUS_NUM tUMINUS
%right tPOW
%right '!' '~' tUPLUS

%token tLAST_TOKEN

/*
 *	inlining rules
 */
%rule %inline ident_or_const
                : tIDENTIFIER
                | tCONSTANT
                ;

%rule %inline user_or_keyword_variable
                : user_variable
                | keyword_variable
                ;

/*
 *	parameterizing rules
 */
%rule asgn(rhs) <node>
                : lhs '=' lex_ctxt rhs
                    {
                        $$ = node_assign(p, (NODE *)$lhs, $rhs, $lex_ctxt, &@$);
                    }
                ;

%rule args_tail_basic(value, trailing) <node_args>
                : f_kwarg(value) ',' f_kwrest opt_f_block_arg(trailing)
                    {
                        $$ = new_args_tail(p, $1, $3, $4, &@3);
                    }
                | f_kwarg(value) opt_f_block_arg(trailing)
                    {
                        $$ = new_args_tail(p, $1, 0, $2, &@1);
                    }
                | f_any_kwrest opt_f_block_arg(trailing)
                    {
                        $$ = new_args_tail(p, 0, $1, $2, &@1);
                    }
                | f_block_arg
                    {
                        $$ = new_args_tail(p, 0, 0, $1, &@1);
                    }
                ;

%rule opt_f_block_arg(trailing) <id>
                : ',' f_block_arg
                    {
                        $$ = $2;
                    }
                | trailing
                ;

%rule def_endless_method(bodystmt) <node>
                : defn_head[head] f_opt_paren_args[args] '=' bodystmt
                    {
                        endless_method_name(p, $head->nd_mid, &@head);
                        restore_defun(p, $head);
                        $$ = 0; YSTUB("endless method definition");
                        $bodystmt = new_scope_body(p, $args, $bodystmt, $$, &@$);
                        local_pop(p);
                    }
                | defs_head[head] f_opt_paren_args[args] '=' bodystmt
                    {
                        endless_method_name(p, $head->nd_mid, &@head);
                        restore_defun(p, $head);
                        $$ = 0; YSTUB("endless singleton method definition");
                        $bodystmt = new_scope_body(p, $args, $bodystmt, $$, &@$);
                        local_pop(p);
                    }
                ;

%rule compstmt(stmts) <node>
                    : stmts terms?
                        {
                            void_stmts(p, $$ = $stmts);
                        }
                    ;

%rule f_opt(value) <node_opt_arg>
                : f_arg_asgn f_eq value
                    {
                        p->ctxt.in_argdef = 1;
                        $$ = NEW_OPT_ARG(assignable(p, $f_arg_asgn, $value, &@f_arg_asgn), &@$);
                    }
                ;

%rule f_opt_arg(value) <node_opt_arg>
                : f_opt(value)
                    {
                        $$ = $f_opt;
                    }
                | f_opt_arg(value) ',' f_opt(value)
                    {
                        $$ = opt_arg_append(p, $f_opt_arg, $f_opt);
                    }
                ;

%rule f_kw(value) <node_kw_arg>
                : f_label value
                    {
                        p->ctxt.in_argdef = 1;
                        assignable(p, $f_label, $value, &@$); /* registers the local */
                        $$ = (rb_node_kw_arg_t *) pm_ykw_param(p, $f_label, $value, &@f_label, &@$);
                    }
                | f_label
                    {
                        p->ctxt.in_argdef = 1;
                        assignable(p, $f_label, 0, &@$); /* registers the local */
                        $$ = (rb_node_kw_arg_t *) pm_ykw_param(p, $f_label, NULL, &@f_label, &@$);
                    }
                ;

%rule f_kwarg(value) <node_kw_arg>
                : f_kw(value)
                    {
                        $$ = $f_kw;
                    }
                | f_kwarg(value) ',' f_kw(value)
                    {
                        $$ = kwd_append(p, $f_kwarg, $f_kw);
                    }
                ;

%rule mlhs_items(item) <node>
                : item
                    {
                        $$ = NEW_LIST($1, &@$);
                    }
                | mlhs_items(item) ',' item
                    {
                        $$ = list_append(p, $1, $3);
                    }
                ;

%rule op_asgn(rhs) <node>
                : var_lhs tOP_ASGN lex_ctxt rhs
                    {
                        $$ = new_op_assign(p, $var_lhs, $tOP_ASGN, $rhs, $lex_ctxt, &@tOP_ASGN, &@$);
                    }
                | primary_value '['[lbracket] opt_call_args rbracket tOP_ASGN lex_ctxt rhs
                    {
                        $$ = new_ary_op_assign(p, $primary_value, $opt_call_args, $tOP_ASGN, $rhs, &@opt_call_args, &@$, &NULL_LOC, &@lbracket, &@rbracket, &@tOP_ASGN);
                    }
                | primary_value call_op tIDENTIFIER tOP_ASGN lex_ctxt rhs
                    {
                        $$ = new_attr_op_assign(p, $primary_value, $call_op, $tIDENTIFIER, $tOP_ASGN, $rhs, &@$, &@call_op, &@tIDENTIFIER, &@tOP_ASGN);
                    }
                | primary_value call_op tCONSTANT tOP_ASGN lex_ctxt rhs
                    {
                        $$ = new_attr_op_assign(p, $primary_value, $call_op, $tCONSTANT, $tOP_ASGN, $rhs, &@$, &@call_op, &@tCONSTANT, &@tOP_ASGN);
                    }
                | primary_value tCOLON2 tIDENTIFIER tOP_ASGN lex_ctxt rhs
                    {
                        $$ = new_attr_op_assign(p, $primary_value, idCOLON2, $tIDENTIFIER, $tOP_ASGN, $rhs, &@$, &@tCOLON2, &@tIDENTIFIER, &@tOP_ASGN);
                    }
                | primary_value tCOLON2 tCONSTANT tOP_ASGN lex_ctxt rhs
                    {
                        YYLTYPE loc = code_loc_gen(&@primary_value, &@tCONSTANT);
                        $$ = new_const_op_assign(p, NEW_COLON2($primary_value, $tCONSTANT, &loc, &@tCOLON2, &@tCONSTANT), $tOP_ASGN, $rhs, $lex_ctxt, &@$);
                    }
                | tCOLON3 tCONSTANT tOP_ASGN lex_ctxt rhs
                    {
                        YYLTYPE loc = code_loc_gen(&@tCOLON3, &@tCONSTANT);
                        $$ = new_const_op_assign(p, NEW_COLON3($tCONSTANT, &loc, &@tCOLON3, &@tCONSTANT), $tOP_ASGN, $rhs, $lex_ctxt, &@$);
                    }
                | backref tOP_ASGN lex_ctxt rhs
                    {
                        VALUE MAYBE_UNUSED(e) = rb_backref_error(p, $backref);
                        $$ = NEW_ERROR(&@$);
                    }
                ;

%rule opt_args_tail(tail, trailing) <node_args>
                : ',' tail
                    {
                        $$ = $tail;
                    }
                | trailing
                    {
                        $$ = new_empty_args_tail(p, &@$);
                    }
                ;

%rule range_expr(range) <node>
                : range tDOT2 range
                    {
                        value_expr(p, $1);
                        value_expr(p, $3);
                        $$ = NEW_DOT2($1, $3, &@$, &@2);
                    }
                | range tDOT3 range
                    {
                        value_expr(p, $1);
                        value_expr(p, $3);
                        $$ = NEW_DOT3($1, $3, &@$, &@2);
                    }
                | range tDOT2
                    {
                        value_expr(p, $1);
                        $$ = NEW_DOT2($1, new_nil_at(p, NULL), &@$, &@2);
                    }
                | range tDOT3
                    {
                        value_expr(p, $1);
                        $$ = NEW_DOT3($1, new_nil_at(p, NULL), &@$, &@2);
                    }
                | tBDOT2 range
                    {
                        value_expr(p, $2);
                        $$ = NEW_DOT2(new_nil_at(p, NULL), $2, &@$, &@1);
                    }
                | tBDOT3 range
                    {
                        value_expr(p, $2);
                        $$ = NEW_DOT3(new_nil_at(p, NULL), $2, &@$, &@1);
                    }
                ;

%rule value_expr(value) <node>
                : value
                    {
                        value_expr(p, $1);
                        $$ = $1;
                    }
                ;

%rule words(begin, word_list) <node>
                : begin ' '+ word_list tSTRING_END
                    {
                        $$ = make_list($word_list, &@$);
                        $$ = pm_yarray_brackets(p, $$, &@begin, &@tSTRING_END, &@$);
                    }
                ;

%%
program		:  {
                        SET_LEX_STATE(EXPR_BEG);
                        local_push(p, ifndef_ripper(1)+0);
                        /* jumps are possible in the top-level loop. */
                        if (!ifndef_ripper(p->do_loop) + 0) init_block_exit(p);
                    }
                  compstmt(top_stmts)
                    {
                        if ($2 && !compile_for_eval) {
                            NODE *node = $2;
                            /* last expression should not be void */
                            if (nd_type_p(node, NODE_BLOCK)) {
                                while (0) { /* PORTME: walk to the last expression */
                                    YSTUB("grammar"); /* PORTME: node = RNODE_BLOCK(node)->nd_next; */
                                }
                                YSTUB("grammar"); /* PORTME: node = RNODE_BLOCK(node)->nd_head; */
                            }
                            node = remove_begin(node);
                            void_expr(p, node);
                        }
                        p->eval_tree = NEW_SCOPE(0, block_append(p, p->eval_tree, $2), NULL, &@$);
                        local_pop(p);
                    }
                ;

top_stmts	: none
                    {
                        $$ = 0;
                    }
                | top_stmt
                    {
                        $$ = newline_node($1);
                    }
                | top_stmts terms top_stmt
                    {
                        $$ = block_append(p, $1, newline_node($3));
                    }
                ;

top_stmt	: stmt
                    {
                        clear_block_exit(p, true);
                        $$ = $1;
                    }
                | keyword_BEGIN begin_block
                    {
                        $$ = $2;
                    }
                ;

block_open	: '{' {$$ = init_block_exit(p);};

begin_block	: block_open compstmt(top_stmts) '}'
                    {
                        restore_block_exit(p, $block_open);
                        p->eval_tree_begin = block_append(p, p->eval_tree_begin,
                                                          NEW_BEGIN($compstmt, &@$));
                        $$ = NEW_BEGIN(0, &@$);
                    }
                ;

bodystmt	: compstmt(stmts)[body]
                  lex_ctxt[ctxt]
                  opt_rescue
                  k_else
                    {
                        if (!$opt_rescue) yyerror1(&@k_else, "else without rescue is useless");
                        next_rescue_context(&p->ctxt, &$ctxt, after_else);
                    }
                  compstmt(stmts)[elsebody]
                    {
                        next_rescue_context(&p->ctxt, &$ctxt, after_ensure);
                    }
                  opt_ensure
                    {
                        YYLTYPE else_loc = { @k_else.beg, @elsebody.end };
                        NODE *else_clause = pm_yelse(p, $elsebody, &@k_else, &else_loc);
                        $$ = new_bodystmt(p, $body, $opt_rescue, else_clause, $opt_ensure, &@$);
                    }
                | compstmt(stmts)[body]
                  lex_ctxt[ctxt]
                  opt_rescue
                    {
                        next_rescue_context(&p->ctxt, &$ctxt, after_ensure);
                    }
                  opt_ensure
                    {
                        $$ = new_bodystmt(p, $body, $opt_rescue, 0, $opt_ensure, &@$);
                    }
                ;

stmts		: none
                    {
                        /* CRuby: an empty NODE_BEGIN as the empty-statements
                         * marker; prism's representation is simply no node. */
                        $$ = 0;
                    }
                | stmt_or_begin
                    {
                        $$ = newline_node($1);
                    }
                | stmts terms stmt_or_begin
                    {
                        $$ = block_append(p, $1, newline_node($3));
                    }
                ;

stmt_or_begin	: stmt
                | keyword_BEGIN
                    {
                        yyerror1(&@1, "BEGIN is permitted only at toplevel");
                    }
                  begin_block
                    {
                        $$ = $3;
                    }
                ;

allow_exits	: {$$ = allow_block_exit(p);};

k_END		: keyword_END lex_ctxt
                    {
                        if (p->ctxt.in_def) {
                            rb_warn0("END in method; use at_exit");
                        }
                        $$ = $2;
                        p->ctxt.in_rescue = before_rescue;
                    };

stmt		: keyword_alias[kw] fitem[new] {SET_LEX_STATE(EXPR_FNAME|EXPR_FITEM);} fitem[old]
                    {
                        $$ = NEW_ALIAS($new, $old, &@$, &@kw);
                    }
                | keyword_alias[kw] tGVAR[new] tGVAR[old]
                    {
                        $$ = NEW_VALIAS($new, $old, &@$, &@kw, &@new, &@old);
                    }
                | keyword_alias[kw] tGVAR[new] tBACK_REF[old]
                    {
                        /* the lexer already built the BackReferenceReadNode */
                        pm_node_t *new_name = (pm_node_t *) pm_global_variable_read_node_new(
                            p->pm->arena, ++p->pm->node_id, 0, pm_yloc(&@new), pm_yid2const(p, $new));
                        $$ = (NODE *) pm_alias_global_variable_node_new(
                            p->pm->arena, ++p->pm->node_id, 0, pm_yloc(&@$),
                            new_name, $old, pm_yloc(&@kw));
                    }
                | keyword_alias tGVAR tNTH_REF[nth]
                    {
                        static const char mesg[] = "can't make alias for the number variables";
                        yyerror1(&@nth, mesg);
                        $$ = NEW_ERROR(&@$);
                    }
                | keyword_undef[kw] undef_list[list]
                    {
                        if ($list != NULL && PM_NODE_TYPE_P($list, PM_UNDEF_NODE)) {
                            pm_undef_node_t *undef = (pm_undef_node_t *) $list;
                            undef->keyword_loc = pm_yloc(&@kw);
                            uint32_t undef_end = undef->base.location.start + undef->base.location.length;
                            undef->base.location = (pm_location_t) { @kw.beg, undef_end - @kw.beg };
                        }
                        $$ = $list;
                    }
                | stmt[body] modifier_if[mod] expr_value[cond]
                    {
                        $$ = new_if(p, $cond, remove_begin($body), 0, &@$, &@mod, &NULL_LOC, &NULL_LOC);
                        fixpos($$, $cond);
                    }
                | stmt[body] modifier_unless[mod] expr_value[cond]
                    {
                        $$ = new_unless(p, $cond, remove_begin($body), 0, &@$, &@mod, &NULL_LOC, &NULL_LOC);
                        fixpos($$, $cond);
                    }
                | stmt[body] modifier_while[mod] expr_value[cond_expr]
                    {
                        clear_block_exit(p, false);
                        if ($body && PM_NODE_TYPE_P($body, PM_BEGIN_NODE)) {
                            /* prism keeps the begin in the body; only the flag differs */
                            $$ = NEW_WHILE(cond(p, $cond_expr, &@cond_expr), $body, 0, &@$, &@mod, &NULL_LOC);
                        }
                        else {
                            $$ = NEW_WHILE(cond(p, $cond_expr, &@cond_expr), $body, 1, &@$, &@mod, &NULL_LOC);
                        }
                    }
                | stmt[body] modifier_until[mod] expr_value[cond_expr]
                    {
                        clear_block_exit(p, 0);
                        if ($body && PM_NODE_TYPE_P($body, PM_BEGIN_NODE)) {
                            /* prism keeps the begin in the body; only the flag differs */
                            $$ = NEW_UNTIL(cond(p, $cond_expr, &@cond_expr), $body, 0, &@$, &@mod, &NULL_LOC);
                        }
                        else {
                            $$ = NEW_UNTIL(cond(p, $cond_expr, &@cond_expr), $body, 1, &@$, &@mod, &NULL_LOC);
                        }
                    }
                | stmt[body] modifier_rescue[mod] after_rescue[ctxt] stmt[resbody]
                    {
                        p->ctxt.in_rescue = $ctxt.in_rescue;
                        $$ = pm_yrescue_modifier(p, remove_begin($body), remove_begin($resbody), &@mod, &@$);
                    }
                | k_END[k_end] block_open[lbrace] compstmt(stmts)[body] '}'[rbrace]
                    {
                        clear_block_exit(p, true);
                        restore_block_exit(p, $block_open);
                        p->ctxt = $k_end;
                        {
                            NODE *scope = NEW_SCOPE2(0 /* tbl */, 0 /* args */, $body /* body */, NULL /* parent */, &@$);
                            $$ = NEW_POSTEXE(scope, &@$, &@k_end, &@lbrace, &@rbrace);
                            YSTUB("grammar"); /* PORTME: RNODE_SCOPE(scope)->nd_parent = $$; */
                        }
                    }
                | command_asgn
                | mlhs[lhs] '=' lex_ctxt[ctxt] command_call_value[rhs]
                    {
                        $$ = node_assign(p, (NODE *)$lhs, $rhs, $ctxt, &@$);
                    }
                | asgn(mrhs)
                | mlhs[lhs] '=' lex_ctxt[lex_ctxt] mrhs_arg[mrhs_arg] modifier_rescue[modifier_rescue]
                  after_rescue[after_rescue] stmt[resbody]
                    {
                        p->ctxt.in_rescue = $after_rescue.in_rescue;
                        YYLTYPE loc = { @mrhs_arg.beg, @resbody.end };
                        $mrhs_arg = pm_yrescue_modifier(p, $mrhs_arg, remove_begin($resbody), &@modifier_rescue, &loc);
                        $$ = node_assign(p, (NODE *)$lhs, $mrhs_arg, $lex_ctxt, &@$);
                    }
                | mlhs[lhs] '=' lex_ctxt[ctxt] mrhs_arg[rhs]
                    {
                        $$ = node_assign(p, (NODE *)$lhs, $rhs, $ctxt, &@$);
                    }
                | expr
                | error
                    {
                        (void)yynerrs;
                        $$ = NEW_ERROR(&@$);
                    }
                ;

command_asgn	: asgn(command_rhs)
                | op_asgn(command_rhs)
                | def_endless_method(endless_command)
                ;

endless_command : command
                | endless_command modifier_rescue after_rescue arg
                    {
                        p->ctxt.in_rescue = $3.in_rescue;
                        $$ = rescued_expr(p, $1, $4, &@1, &@2, &@4);
                    }
                | keyword_not '\n'? endless_command
                    {
                        $$ = call_uni_op(p, method_cond(p, $3, &@3), METHOD_NOT, &@1, &@$);
                    }
                ;

command_rhs	: command_call_value   %prec tOP_ASGN
                | command_call_value modifier_rescue after_rescue stmt
                    {
                        p->ctxt.in_rescue = $3.in_rescue;
                        YYLTYPE loc = code_loc_gen(&@2, &@4);
                        $$ = NEW_RESCUE($1, NEW_RESBODY(0, 0, remove_begin($4), 0, &loc), 0, &@$);
                    }
                | command_asgn
                ;

expr		: command_call
                | expr[left] keyword_and[op] expr[right]
                    {
                        $$ = logop(p, idAND, $left, $right, &@op, &@$);
                    }
                | expr[left] keyword_or[op] expr[right]
                    {
                        $$ = logop(p, idOR, $left, $right, &@op, &@$);
                    }
                | keyword_not[not] '\n'? expr[arg]
                    {
                        $$ = call_uni_op(p, method_cond(p, $arg, &@arg), METHOD_NOT, &@not, &@$);
                    }
                | '!'[not] command_call[arg]
                    {
                        $$ = call_uni_op(p, method_cond(p, $arg, &@arg), '!', &@not, &@$);
                    }
                | arg tASSOC[assoc]
                    {
                        value_expr(p, $arg);
                    }
                  p_in_kwarg[ctxt] p_pvtbl p_pktbl
                  p_top_expr_body[body]
                    {
                        pop_pktbl(p, $p_pktbl);
                        pop_pvtbl(p, $p_pvtbl);
                        p->ctxt.in_kwarg = $ctxt.in_kwarg;
                        p->ctxt.in_alt_pattern = $ctxt.in_alt_pattern;
                        p->ctxt.capture_in_pattern = $ctxt.capture_in_pattern;
                        $$ = NEW_CASE3($arg, NEW_IN($body, 0, 0, &@body, &NULL_LOC, &NULL_LOC, &@assoc), &@$, &NULL_LOC, &NULL_LOC);
                    }
                | arg keyword_in
                    {
                        value_expr(p, $arg);
                    }
                  p_in_kwarg[ctxt] p_pvtbl p_pktbl
                  p_top_expr_body[body]
                    {
                        pop_pktbl(p, $p_pktbl);
                        pop_pvtbl(p, $p_pvtbl);
                        p->ctxt.in_kwarg = $ctxt.in_kwarg;
                        p->ctxt.in_alt_pattern = $ctxt.in_alt_pattern;
                        p->ctxt.capture_in_pattern = $ctxt.capture_in_pattern;
                        $$ = NEW_CASE3($arg, NEW_IN($body, NEW_TRUE(&@body), NEW_FALSE(&@body), &@body, &@keyword_in, &NULL_LOC, &NULL_LOC), &@$, &NULL_LOC, &NULL_LOC);
                    }
                | arg %prec tLBRACE_ARG
                ;

def_name	: fname
                    {
                        numparam_name(p, $fname);
                        local_push(p, 0);
                        p->ctxt.in_def = 1;
                        p->ctxt.in_rescue = before_rescue;
                        p->ctxt.cant_return = 0;
                        $$ = $fname;
                    }
                ;

defn_head	: k_def def_name
                    {
                        $$ = def_head_save(p, $k_def);
                        $$->nd_mid = $def_name;
                        $$->nd_def = NEW_DEFN($def_name, 0, &@$);
                        pm_ydef_head(p, $$->nd_def, &@k_def, NULL, &@def_name);
                    }
                ;

defs_head	: k_def singleton dot_or_colon
                    {
                        SET_LEX_STATE(EXPR_FNAME);
                    }
                  def_name
                    {
                        SET_LEX_STATE(EXPR_ENDFN|EXPR_LABEL); /* force for args */
                        $$ = def_head_save(p, $k_def);
                        $$->nd_mid = $def_name;
                        $$->nd_def = NEW_DEFS($singleton, $def_name, 0, &@$);
                        pm_ydef_head(p, $$->nd_def, &@k_def, &@dot_or_colon, &@def_name);
                    }
                ;

expr_value	: value_expr(expr)
                | error
                    {
                        $$ = NEW_ERROR(&@$);
                    }
                ;

expr_value_do	: {COND_PUSH(1);} expr_value do {COND_POP();}
                    {
                        $$ = $2;
                    }
                ;

command_call	: command
                | block_command
                ;

command_call_value	: value_expr(command_call)
                    ;

block_command	: block_call
                | block_call call_op2 operation2 command_args
                    {
                        $$ = new_qcall(p, $2, $1, $3, $4, &@3, &@$);
                    }
                ;

cmd_brace_block	: tLBRACE_ARG brace_body '}'
                    {
                        $$ = $2;
                        set_embraced_location($$, &@1, &@3);
                    }
                ;

fcall		: operation
                    {
                        $$ = NEW_FCALL($1, 0, &@$);
                    }
                ;

command		: fcall command_args       %prec tLOWEST
                    {
                        $$ = pm_yfcall_args(p, (NODE *)$1, $2, &@$);
                    }
                | fcall command_args cmd_brace_block
                    {
                        block_dup_check(p, $2, $3);
                        YSTUB("grammar"); /* PORTME: $1->nd_args = $2; */
                        $$ = method_add_block(p, (NODE *)$1, $3, &@$);
                        fixpos($$, RNODE($1));
                        YSTUB("grammar"); /* PORTME: nd_set_last_loc($1, @2.end_pos); */
                    }
                | primary_value call_op operation2 command_args	%prec tLOWEST
                    {
                        $$ = new_command_qcall(p, $2, $1, $3, $4, 0, &@3, &@$);
                    }
                | primary_value call_op operation2 command_args cmd_brace_block
                    {
                        $$ = new_command_qcall(p, $2, $1, $3, $4, $5, &@3, &@$);
                    }
                | primary_value tCOLON2 operation2 command_args	%prec tLOWEST
                    {
                        $$ = new_command_qcall(p, idCOLON2, $1, $3, $4, 0, &@3, &@$);
                    }
                | primary_value tCOLON2 operation2 command_args cmd_brace_block
                    {
                        $$ = new_command_qcall(p, idCOLON2, $1, $3, $4, $5, &@3, &@$);
                   }
                | primary_value tCOLON2 tCONSTANT '{' brace_body '}'
                    {
                        set_embraced_location($5, &@4, &@6);
                        $$ = new_command_qcall(p, idCOLON2, $1, $3, 0, $5, &@3, &@$);
                   }
                | keyword_super command_args
                    {
                        $$ = NEW_SUPER($2, &@$, &@1, &NULL_LOC, &NULL_LOC);
                        fixpos($$, $2);
                    }
                | k_yield command_args
                    {
                        $$ = NEW_YIELD($2, &@$, &@1, &NULL_LOC, &NULL_LOC);
                        fixpos($$, $2);
                    }
                | k_return call_args
                    {
                        $$ = NEW_RETURN(ret_args(p, $2), &@$, &@1);
                    }
                | keyword_break call_args
                    {
                        NODE *args = 0;
                        args = ret_args(p, $2);
                        $$ = add_block_exit(p, NEW_BREAK(args, &@$, &@1));
                    }
                | keyword_next call_args
                    {
                        NODE *args = 0;
                        args = ret_args(p, $2);
                        $$ = add_block_exit(p, NEW_NEXT(args, &@$, &@1));
                    }
                ;

mlhs		: mlhs_basic
                | tLPAREN mlhs_inner rparen
                    {
                        $$ = $2;
                        pm_ymulti_parens(p, (NODE *) $$, &@1, &@3);
                    }
                ;

mlhs_inner	: mlhs_basic
                | tLPAREN mlhs_inner rparen
                    {
                        $$ = NEW_MASGN(NEW_LIST((NODE *)$2, &@$), 0, &@$);
                    }
                ;

mlhs_basic	: mlhs_head
                    {
                        $$ = NEW_MASGN($1, 0, &@$);
                    }
                | mlhs_head mlhs_item
                    {
                        $$ = NEW_MASGN(list_append(p, $1, $2), 0, &@$);
                    }
                | mlhs_head tSTAR mlhs_node
                    {
                        $$ = NEW_MASGN($1, $3, &@$);
                    }
                | mlhs_head tSTAR mlhs_node ',' mlhs_items(mlhs_item)
                    {
                        $$ = NEW_MASGN($1, NEW_POSTARG($3,$5,&@$), &@$);
                    }
                | mlhs_head tSTAR
                    {
                        $$ = NEW_MASGN($1, NODE_SPECIAL_NO_NAME_REST, &@$);
                    }
                | mlhs_head tSTAR ',' mlhs_items(mlhs_item)
                    {
                        $$ = NEW_MASGN($1, NEW_POSTARG(NODE_SPECIAL_NO_NAME_REST, $4, &@$), &@$);
                    }
                | tSTAR mlhs_node
                    {
                        $$ = NEW_MASGN(0, $2, &@$);
                    }
                | tSTAR mlhs_node ',' mlhs_items(mlhs_item)
                    {
                        $$ = NEW_MASGN(0, NEW_POSTARG($2,$4,&@$), &@$);
                    }
                | tSTAR
                    {
                        $$ = NEW_MASGN(0, NODE_SPECIAL_NO_NAME_REST, &@$);
                    }
                | tSTAR ',' mlhs_items(mlhs_item)
                    {
                        $$ = NEW_MASGN(0, NEW_POSTARG(NODE_SPECIAL_NO_NAME_REST, $3, &@$), &@$);
                    }
                ;

mlhs_item	: mlhs_node
                | tLPAREN mlhs_inner rparen
                    {
                        $$ = (NODE *)$2;
                        pm_ymulti_parens(p, $$, &@1, &@3);
                    }
                ;

mlhs_head	: mlhs_item ','
                    {
                        $$ = NEW_LIST($1, &@1);
                    }
                | mlhs_head mlhs_item ','
                    {
                        $$ = list_append(p, $1, $2);
                    }
                ;


mlhs_node	: user_or_keyword_variable
                    {
                        $$ = assignable(p, $1, 0, &@$);
                    }
                | primary_value '[' opt_call_args rbracket
                    {
                        $$ = aryset(p, $1, $3, &@$);
                        $$ = pm_yindex_call(p, $$, &@2, &@4);
                    }
                | primary_value call_op ident_or_const
                    {
                        anddot_multiple_assignment_check(p, &@2, $2);
                        $$ = attrset(p, $1, $2, $3, &@$);
                    }
                | primary_value tCOLON2 tIDENTIFIER
                    {
                        $$ = attrset(p, $1, idCOLON2, $3, &@$);
                    }
                | primary_value tCOLON2 tCONSTANT
                    {
                        $$ = const_decl(p, NEW_COLON2($1, $3, &@$, &@2, &@3), &@$);
                    }
                | tCOLON3 tCONSTANT
                    {
                        $$ = const_decl(p, NEW_COLON3($2, &@$, &@1, &@2), &@$);
                    }
                | backref
                    {
                        VALUE MAYBE_UNUSED(e) = rb_backref_error(p, $1);
                        $$ = NEW_ERROR(&@$);
                    }
                ;

lhs		: user_or_keyword_variable
                    {
                        $$ = assignable(p, $1, 0, &@$);
                    }
                | primary_value '[' opt_call_args rbracket
                    {
                        $$ = aryset(p, $1, $3, &@$);
                        $$ = pm_yindex_call(p, $$, &@2, &@4);
                    }
                | primary_value call_op ident_or_const
                    {
                        $$ = attrset(p, $1, $2, $3, &@$);
                    }
                | primary_value tCOLON2 tIDENTIFIER
                    {
                        $$ = attrset(p, $1, idCOLON2, $3, &@$);
                    }
                | primary_value tCOLON2 tCONSTANT
                    {
                        $$ = const_decl(p, NEW_COLON2($1, $3, &@$, &@2, &@3), &@$);
                    }
                | tCOLON3 tCONSTANT
                    {
                        $$ = const_decl(p, NEW_COLON3($2, &@$, &@1, &@2), &@$);
                    }
                | backref
                    {
                        VALUE MAYBE_UNUSED(e) = rb_backref_error(p, $1);
                        $$ = NEW_ERROR(&@$);
                    }
                ;

cname		: tIDENTIFIER
                    {
                        static const char mesg[] = "class/module name must be CONSTANT";
                        yyerror1(&@1, mesg);
                    }
                | tCONSTANT
                ;

cpath		: tCOLON3 cname
                    {
                        $$ = NEW_COLON3($2, &@$, &@1, &@2);
                    }
                | cname
                    {
                        $$ = NEW_COLON2(0, $1, &@$, &NULL_LOC, &@1);
                    }
                | primary_value tCOLON2 cname
                    {
                        $$ = NEW_COLON2($1, $3, &@$, &@2, &@3);
                    }
                ;

fname		: operation
                | op
                    {
                        SET_LEX_STATE(EXPR_ENDFN);
                        $$ = $1;
                    }
                | reswords
                ;

fitem		: fname
                    {
                        $$ = NEW_SYM(rb_id2str($1), &@$);
                    }
                | symbol
                ;

undef_list	: fitem
                    {
                        $$ = NEW_UNDEF($1, &@$);
                    }
                | undef_list ',' {SET_LEX_STATE(EXPR_FNAME|EXPR_FITEM);} fitem
                    {
                        if ($1 != NULL && $4 != NULL && PM_NODE_TYPE_P($1, PM_UNDEF_NODE)) {
                            pm_undef_node_t *undef = (pm_undef_node_t *) $1;
                            pm_node_list_append(p->pm->arena, &undef->names, $4);
                            uint32_t undef_end = $4->location.start + $4->location.length;
                            undef->base.location.length = undef_end - undef->base.location.start;
                        }
                        $$ = $1;
                    }
                ;

op		: '|'		{ $$ = '|'; }
                | '^'		{ $$ = '^'; }
                | '&'		{ $$ = '&'; }
                | tCMP		{ $$ = tCMP; }
                | tEQ		{ $$ = tEQ; }
                | tEQQ		{ $$ = tEQQ; }
                | tMATCH	{ $$ = tMATCH; }
                | tNMATCH	{ $$ = tNMATCH; }
                | '>'		{ $$ = '>'; }
                | tGEQ		{ $$ = tGEQ; }
                | '<'		{ $$ = '<'; }
                | tLEQ		{ $$ = tLEQ; }
                | tNEQ		{ $$ = tNEQ; }
                | tLSHFT	{ $$ = tLSHFT; }
                | tRSHFT	{ $$ = tRSHFT; }
                | '+'		{ $$ = '+'; }
                | '-'		{ $$ = '-'; }
                | '*'		{ $$ = '*'; }
                | tSTAR		{ $$ = '*'; }
                | '/'		{ $$ = '/'; }
                | '%'		{ $$ = '%'; }
                | tPOW		{ $$ = tPOW; }
                | tDSTAR	{ $$ = tDSTAR; }
                | '!'		{ $$ = '!'; }
                | '~'		{ $$ = '~'; }
                | tUPLUS	{ $$ = tUPLUS; }
                | tUMINUS	{ $$ = tUMINUS; }
                | tAREF		{ $$ = tAREF; }
                | tASET		{ $$ = tASET; }
                | '`'		{ $$ = '`'; }
                ;

reswords	: keyword__LINE__ | keyword__FILE__ | keyword__ENCODING__
                | keyword_BEGIN | keyword_END
                | keyword_alias | keyword_and | keyword_begin
                | keyword_break | keyword_case | keyword_class | keyword_def
                | keyword_defined | keyword_do | keyword_else | keyword_elsif
                | keyword_end | keyword_ensure | keyword_false
                | keyword_for | keyword_in | keyword_module | keyword_next
                | keyword_nil | keyword_not | keyword_or | keyword_redo
                | keyword_rescue | keyword_retry | keyword_return | keyword_self
                | keyword_super | keyword_then | keyword_true | keyword_undef
                | keyword_when | keyword_yield | keyword_if | keyword_unless
                | keyword_while | keyword_until
                ;

arg		: asgn(arg_rhs)
                | op_asgn(arg_rhs)
                | range_expr(arg)
                | arg '+' arg
                    {
                        $$ = call_bin_op(p, $1, '+', $3, &@2, &@$);
                    }
                | arg '-' arg
                    {
                        $$ = call_bin_op(p, $1, '-', $3, &@2, &@$);
                    }
                | arg '*' arg
                    {
                        $$ = call_bin_op(p, $1, '*', $3, &@2, &@$);
                    }
                | arg '/' arg
                    {
                        $$ = call_bin_op(p, $1, '/', $3, &@2, &@$);
                    }
                | arg '%' arg
                    {
                        $$ = call_bin_op(p, $1, '%', $3, &@2, &@$);
                    }
                | arg tPOW arg
                    {
                        $$ = call_bin_op(p, $1, idPow, $3, &@2, &@$);
                    }
                | tUMINUS_NUM simple_numeric tPOW arg
                    {
                        /* the power binds tighter: -(2 ** n), so the inner
                         * call spans from the numeric, not the minus */
                        YYLTYPE pow_loc = { @2.beg, @4.end };
                        $$ = call_uni_op(p, call_bin_op(p, $2, idPow, $4, &@3, &pow_loc), idUMinus, &@1, &@$);
                    }
                | tUPLUS arg
                    {
                        $$ = call_uni_op(p, $2, idUPlus, &@1, &@$);
                    }
                | tUMINUS arg
                    {
                        $$ = call_uni_op(p, $2, idUMinus, &@1, &@$);
                    }
                | arg '|' arg
                    {
                        $$ = call_bin_op(p, $1, '|', $3, &@2, &@$);
                    }
                | arg '^' arg
                    {
                        $$ = call_bin_op(p, $1, '^', $3, &@2, &@$);
                    }
                | arg '&' arg
                    {
                        $$ = call_bin_op(p, $1, '&', $3, &@2, &@$);
                    }
                | arg tCMP arg
                    {
                        $$ = call_bin_op(p, $1, idCmp, $3, &@2, &@$);
                    }
                | rel_expr   %prec tCMP
                | arg tEQ arg
                    {
                        $$ = call_bin_op(p, $1, idEq, $3, &@2, &@$);
                    }
                | arg tEQQ arg
                    {
                        $$ = call_bin_op(p, $1, idEqq, $3, &@2, &@$);
                    }
                | arg tNEQ arg
                    {
                        $$ = call_bin_op(p, $1, idNeq, $3, &@2, &@$);
                    }
                | arg tMATCH arg
                    {
                        $$ = match_op(p, $1, $3, &@2, &@$);
                    }
                | arg tNMATCH arg
                    {
                        $$ = call_bin_op(p, $1, idNeqTilde, $3, &@2, &@$);
                    }
                | '!' arg
                    {
                        $$ = call_uni_op(p, method_cond(p, $2, &@2), '!', &@1, &@$);
                    }
                | '~' arg
                    {
                        $$ = call_uni_op(p, $2, '~', &@1, &@$);
                    }
                | arg tLSHFT arg
                    {
                        $$ = call_bin_op(p, $1, idLTLT, $3, &@2, &@$);
                    }
                | arg tRSHFT arg
                    {
                        $$ = call_bin_op(p, $1, idGTGT, $3, &@2, &@$);
                    }
                | arg tANDOP arg
                    {
                        $$ = logop(p, idANDOP, $1, $3, &@2, &@$);
                    }
                | arg tOROP arg
                    {
                        $$ = logop(p, idOROP, $1, $3, &@2, &@$);
                    }
                | keyword_defined '\n'? begin_defined arg
                    {
                        p->ctxt.in_defined = $3.in_defined;
                        $$ = new_defined(p, $4, &@$, &@1);
                        p->ctxt.has_trailing_semicolon = $3.has_trailing_semicolon;
                    }
                | def_endless_method(endless_arg)
                | ternary
                | primary
                ;

ternary		: arg '?' arg '\n'? ':' arg
                    {
                        value_expr(p, $1);
                        {
                            YYLTYPE else_loc = { @5.beg, @6.end };
                            NODE *else_clause = pm_yelse(p, $6, &@5, &else_loc);
                            $$ = new_if(p, $1, $3, else_clause, &@$, &NULL_LOC, &@2, &NULL_LOC);
                        }
                        fixpos($$, $1);
                    }
                ;

endless_arg	: arg %prec modifier_rescue
                | endless_arg modifier_rescue after_rescue arg
                    {
                        p->ctxt.in_rescue = $3.in_rescue;
                        $$ = rescued_expr(p, $1, $4, &@1, &@2, &@4);
                    }
                | keyword_not '\n'? endless_arg
                    {
                        $$ = call_uni_op(p, method_cond(p, $3, &@3), METHOD_NOT, &@1, &@$);
                    }
                ;

relop		: '>'  {$$ = '>';}
                | '<'  {$$ = '<';}
                | tGEQ {$$ = idGE;}
                | tLEQ {$$ = idLE;}
                ;

rel_expr	: arg relop arg   %prec '>'
                    {
                        $$ = call_bin_op(p, $1, $2, $3, &@2, &@$);
                    }
                | rel_expr relop arg   %prec '>'
                    {
                        rb_warning1("comparison '%s' after comparison", WARN_ID($2));
                        $$ = call_bin_op(p, $1, $2, $3, &@2, &@$);
                    }
                ;

lex_ctxt	: none
                    {
                        $$ = p->ctxt;
                    }
                ;

begin_defined	: lex_ctxt
                    {
                        p->ctxt.in_defined = 1;
                        $$ = $1;
                    }
                ;

after_rescue	: lex_ctxt
                    {
                        p->ctxt.in_rescue = after_rescue;
                        $$ = $1;
                    }
                ;

arg_value	: value_expr(arg)
                ;

aref_args	: none
                | args trailer
                | args ',' assocs trailer
                    {
                        $$ = $3 ? arg_append(p, $1, new_hash(p, $3, &@3), &@$) : $1;
                    }
                | assocs trailer
                    {
                        $$ = $1 ? NEW_LIST(new_hash(p, $1, &@1), &@$) : 0;
                    }
                ;

arg_rhs 	: arg   %prec tOP_ASGN
                    {
                        value_expr(p, $1);
                        $$ = $1;
                    }
                | arg modifier_rescue after_rescue arg
                    {
                        p->ctxt.in_rescue = $3.in_rescue;
                        value_expr(p, $1);
                        $$ = rescued_expr(p, $1, $4, &@1, &@2, &@4);
                    }
                ;

paren_args	: '(' opt_call_args rparen
                    {
                        $$ = $2;
                        pm_yparens_set(p, &@1, &@3);
                    }
                | '(' args ',' args_forward rparen
                    {
                        if (!check_forwarding_args(p)) {
                            $$ = 0;
                        }
                        else {
                            $$ = new_args_forward_call(p, $2, &@4, &@$);
                        }
                    }
                | '(' args_forward rparen
                    {
                        if (!check_forwarding_args(p)) {
                            $$ = 0;
                        }
                        else {
                            $$ = new_args_forward_call(p, 0, &@2, &@$);
                        }
                    }
                ;

opt_paren_args	: none
                | paren_args
                    {
                        $$ = $1 ? $1 : NODE_SPECIAL_EMPTY_ARGS;
                    }
                ;

opt_call_args	: none
                | call_args
                | args ','
                | args ',' assocs ','
                    {
                        $$ = $3 ? arg_append(p, $1, new_hash(p, $3, &@3), &@$) : $1;
                    }
                | assocs ','
                    {
                        $$ = $1 ? NEW_LIST(new_hash(p, $1, &@1), &@1) : 0;
                    }
                ;

call_args	: value_expr(command)
                    {
                        $$ = NEW_LIST($1, &@$);
                    }
                | def_endless_method(endless_command)
                    {
                        $$ = NEW_LIST($1, &@$);
                    }
                | args opt_block_arg
                    {
                        $$ = arg_blk_pass(p, $1, $2);
                    }
                | assocs opt_block_arg
                    {
                        $$ = $1 ? NEW_LIST(new_hash(p, $1, &@1), &@1) : 0;
                        $$ = arg_blk_pass(p, $$, $2);
                    }
                | args ',' assocs opt_block_arg
                    {
                        $$ = $3 ? arg_append(p, $1, new_hash(p, $3, &@3), &@$) : $1;
                        $$ = arg_blk_pass(p, $$, $4);
                    }
                | block_arg
                    {
                        /* fork: a lone &block also parks; there is no list */
                        $$ = arg_blk_pass(p, 0, (rb_node_block_pass_t *) $1);
                    }
                ;

command_args	:   {
                        /* If call_args starts with a open paren '(' or '[',
                         * look-ahead reading of the letters calls CMDARG_PUSH(0),
                         * but the push must be done after CMDARG_PUSH(1).
                         * So this code makes them consistent by first cancelling
                         * the premature CMDARG_PUSH(0), doing CMDARG_PUSH(1),
                         * and finally redoing CMDARG_PUSH(0).
                         */
                        int lookahead = 0;
                        switch (yychar) {
                          case '(': case tLPAREN: case tLPAREN_ARG: case '[': case tLBRACK:
                            lookahead = 1;
                        }
                        if (lookahead) CMDARG_POP();
                        CMDARG_PUSH(1);
                        if (lookahead) CMDARG_PUSH(0);
                    }
                  call_args
                    {
                        /* call_args can be followed by tLBRACE_ARG (that does CMDARG_PUSH(0) in the lexer)
                         * but the push must be done after CMDARG_POP() in the parser.
                         * So this code does CMDARG_POP() to pop 0 pushed by tLBRACE_ARG,
                         * CMDARG_POP() to pop 1 pushed by command_args,
                         * and CMDARG_PUSH(0) to restore back the flag set by tLBRACE_ARG.
                         */
                        int lookahead = 0;
                        switch (yychar) {
                          case tLBRACE_ARG:
                            lookahead = 1;
                        }
                        if (lookahead) CMDARG_POP();
                        CMDARG_POP();
                        if (lookahead) CMDARG_PUSH(0);
                        $$ = $2;
                    }
                ;

block_arg	: tAMPER arg_value
                    {
                        $$ = NEW_BLOCK_PASS($2, &@$, &@1);
                    }
                | tAMPER
                    {
                        forwarding_arg_check(p, idFWD_BLOCK, idFWD_ALL, "block");
                        $$ = NEW_BLOCK_PASS(NEW_LVAR(idFWD_BLOCK, &@1), &@$, &@1);
                    }
                ;

opt_block_arg	: ',' block_arg
                    {
                        $$ = $2;
                    }
                | none
                    {
                        $$ = 0;
                    }
                ;

/* value */
args		: arg_value
                    {
                        $$ = NEW_LIST($arg_value, &@$);
                    }
                | arg_splat
                    {
                        $$ = $arg_splat;
                    }
                | args[non_last_args] ',' arg_value
                    {
                        $$ = last_arg_append(p, $non_last_args, $arg_value, &@$);
                    }
                | args[non_last_args] ',' arg_splat
                    {
                        $$ = rest_arg_append(p, $non_last_args, $arg_splat, &@$);
                    }
                ;

/* value */
arg_splat	: tSTAR arg_value
                    {
                        $$ = NEW_SPLAT($arg_value, &@$, &@tSTAR);
                    }
                | tSTAR /* none */
                    {
                        forwarding_arg_check(p, idFWD_REST, idFWD_ALL, "rest");
                        $$ = NEW_SPLAT(NEW_LVAR(idFWD_REST, &@tSTAR), &@$, &@tSTAR);
                    }
                ;

/* value */
mrhs_arg	: mrhs
                | arg_value
                ;

/* value */
mrhs		: args ',' arg_value
                    {
                        $$ = last_arg_append(p, $args, $arg_value, &@$);
                    }
                | args ',' tSTAR arg_value
                    {
                        $$ = rest_arg_append(p, $args, $arg_value, &@$);
                    }
                | tSTAR arg_value
                    {
                        $$ = NEW_SPLAT($arg_value, &@$, &@tSTAR);
                    }
                ;

%rule %inline inline_primary
                : literal
                | strings
                | xstring
                | regexp
                | words
                | qwords
                | symbols
                | qsymbols
                ;

primary		: inline_primary
            | var_ref
            | backref
            | tFID[fid]
                {
                    $$ = (NODE *)NEW_FCALL($fid, 0, &@$);
                }
            | k_begin[kw]
                {
                    CMDARG_PUSH(0);
                }
              bodystmt[body]
              k_end[k_end]
                {
                    CMDARG_POP();
                    $$ = NEW_BEGIN($body, &@$);
                    $$ = pm_ybegin_keywords(p, $$, &@kw, &@k_end);
                }
            | tLPAREN_ARG compstmt(stmts)[body] {SET_LEX_STATE(EXPR_ENDARG);} ')'
                {
                    $$ = pm_yparentheses(p, $body, &@1, &@4, &@$);
                }
            | tLPAREN compstmt(stmts)[body] ')'
                {
                    $$ = pm_yparentheses(p, $body, &@1, &@3, &@$);
                }
            | primary_value[recv] tCOLON2[op] tCONSTANT[name]
                {
                    $$ = NEW_COLON2($recv, $name, &@$, &@op, &@name);
                }
            | tCOLON3[top] tCONSTANT[name]
                {
                    $$ = NEW_COLON3($name, &@$, &@top, &@name);
                }
            | tLBRACK aref_args[args] ']'
                {
                    $$ = make_list($args, &@$);
                    $$ = pm_yarray_brackets(p, $$, &@1, &@3, &@$);
                }
            | tLBRACE assoc_list[list] '}'
                {
                    $$ = new_hash(p, $list, &@$);
                    $$ = pm_yhash_braces(p, $$, &@1, &@3, &@$);
                }
            | k_return[kw]
                {
                    $$ = NEW_RETURN(0, &@$, &@kw);
                }
            | k_yield[kw] '('[lpar] call_args[args] rparen[rpar]
                {
                    $$ = NEW_YIELD($args, &@$, &@kw, &@lpar, &@rpar);
                }
            | k_yield[kw] '('[lpar] rparen[rpar]
                {
                    $$ = NEW_YIELD(0, &@$, &@kw, &@lpar, &@rpar);
                }
            | k_yield[kw]
                {
                    $$ = NEW_YIELD(0, &@$, &@kw, &NULL_LOC, &NULL_LOC);
                }
            | keyword_defined[kw] '\n'? '(' begin_defined[ctxt] expr[arg] rparen
                {
                    p->ctxt.in_defined = $ctxt.in_defined;
                    $$ = new_defined(p, $arg, &@$, &@kw);
                    if ($$ != NULL && PM_NODE_TYPE_P($$, PM_DEFINED_NODE)) {
                        ((pm_defined_node_t *) $$)->lparen_loc = pm_yloc(&@3);
                        ((pm_defined_node_t *) $$)->rparen_loc = pm_yloc(&@rparen);
                    }
                    p->ctxt.has_trailing_semicolon = $ctxt.has_trailing_semicolon;
                }
            | keyword_not[kw] '(' expr[arg] rparen
                {
                    $$ = call_uni_op(p, method_cond(p, $arg, &@arg), METHOD_NOT, &@kw, &@$);
                }
            | keyword_not[kw] '('[lpar] rparen
                {
                    $$ = call_uni_op(p, method_cond(p, NEW_NIL(&@lpar), &@lpar), METHOD_NOT, &@kw, &@$);
                }
            | fcall[call] brace_block[block]
                {
                    $$ = method_add_block(p, (NODE *)$call, $block, &@$);
                }
            | method_call
            | method_call[call] brace_block[block]
                {
                    block_dup_check(p, get_nd_args(p, $call), $block);
                    $$ = method_add_block(p, $call, $block, &@$);
                }
            | lambda
            | k_if[kw] expr_value[cond] then[then]
              compstmt(stmts)[body]
              if_tail[tail]
              k_end[k_end]
                {
                    $$ = new_if(p, $cond, $body, $tail, &@$, &@kw, &@then, &@k_end);
                    fixpos($$, $cond);
                }
            | k_unless[kw] expr_value[cond] then[then]
              compstmt(stmts)[body]
              opt_else[tail]
              k_end[k_end]
                {
                    $$ = new_unless(p, $cond, $body, $tail, &@$, &@kw, &@then, &@k_end);
                    fixpos($$, $cond);
                }
            | k_while[kw] expr_value_do[cond]
              compstmt(stmts)[body]
              k_end[k_end]
                {
                    restore_block_exit(p, $kw);
                    $$ = NEW_WHILE(cond(p, $cond, &@cond), $body, 1, &@$, &@kw, &@k_end);
                    fixpos($$, $cond);
                }
            | k_until[kw] expr_value_do[cond]
              compstmt(stmts)[body]
              k_end[k_end]
                {
                    restore_block_exit(p, $kw);
                    $$ = NEW_UNTIL(cond(p, $cond, &@cond), $body, 1, &@$, &@kw, &@k_end);
                    fixpos($$, $cond);
                }
            | k_case[k_case] expr_value[expr] terms?
                {
                    $$ = p->case_labels;
                    p->case_labels = CHECK_LITERAL_WHEN;
                }[labels]<labels>
              case_body[body]
              k_end[k_end]
                {
                    if (CASE_LABELS_ENABLED_P(p->case_labels)) st_free_table(p->case_labels);
                    p->case_labels = $labels;
                    $$ = NEW_CASE($expr, $body, &@$, &@k_case, &@k_end);
                    fixpos($$, $expr);
                }
            | k_case[k_case] terms?
                {
                    $$ = p->case_labels;
                    p->case_labels = 0;
                }[labels]<labels>
              case_body[body]
              k_end[k_end]
                {
                    if (p->case_labels) st_free_table(p->case_labels);
                    p->case_labels = $labels;
                    $$ = NEW_CASE2($body, &@$, &@k_case, &@k_end);
                }
            | k_case[k_case] expr_value[expr] terms?
              p_case_body[body]
              k_end[k_end]
                {
                    $$ = NEW_CASE3($expr, $body, &@$, &@k_case, &@k_end);
                }
            | k_for[k_for] for_var[for_var] keyword_in[keyword_in]
              {COND_PUSH(1);} expr_value[expr_value] do[do] {COND_POP();}
              compstmt(stmts)[compstmt]
              k_end[k_end]
                {
                    restore_block_exit(p, $k_for);
                    /*
                     *  for a, b, c in e
                     *  #=>
                     *  e.each{|*x| a, b, c = x}
                     *
                     *  for a in e
                     *  #=>
                     *  e.each{|x| a, = x}
                     */
                    ID id = internal_id(p);
                    rb_node_args_aux_t *m = NEW_ARGS_AUX(0, 0, &NULL_LOC);
                    rb_node_args_t *args;
                    NODE *scope, *internal_var = NEW_DVAR(id, &@for_var);
                    rb_ast_id_table_t *tbl = NULL;
                    YSTUB("for loop"); /* PORTME: single-slot local table for the internal variable */

                    switch (nd_type($for_var)) {
                      case NODE_LASGN:
                      case NODE_DASGN: /* e.each {|internal_var| a = internal_var; ... } */
                        set_nd_value(p, $for_var, internal_var);
                        id = 0;
                        YSTUB("grammar"); /* PORTME: m->nd_plen = 1; */
                        YSTUB("grammar"); /* PORTME: m->nd_next = $for_var; */
                        break;
                      case NODE_MASGN: /* e.each {|*internal_var| a, b, c = (internal_var.length == 1 && Array === (tmp = internal_var[0]) ? tmp : internal_var); ... } */
                        YSTUB("grammar"); /* PORTME: m->nd_next = node_assign(p, $for_var, NEW_FOR_MASGN(internal_var, &@for_var), NO_LEX_CTXT, &@for_var */
                        break;
                      default: /* e.each {|*internal_var| @a, B, c[1], d.attr = internal_val; ... } */
                        YSTUB("grammar"); /* PORTME: m->nd_next = node_assign(p, (NODE *)NEW_MASGN(NEW_LIST($for_var, &@for_var), 0, &@for_var), internal */
                    }
                    /* {|*internal_id| <m> = internal_id; ... } */
                    args = new_args(p, m, 0, id, 0, new_empty_args_tail(p, &@for_var), &@for_var);
                    scope = NEW_SCOPE2(tbl, args, $compstmt, NULL, &@$);
                    YYLTYPE do_keyword_loc = $do == keyword_do_cond ? @do : NULL_LOC;
                    $$ = NEW_FOR($expr_value, scope, &@$, &@k_for, &@keyword_in, &do_keyword_loc, &@k_end);
                    YSTUB("grammar"); /* PORTME: RNODE_SCOPE(scope)->nd_parent = $$; */
                    fixpos($$, $for_var);
                }
            | k_class cpath superclass
                {
                    begin_definition("class", &@k_class, &@cpath);
                }
              bodystmt
              k_end
                {
                    YYLTYPE inheritance_operator_loc = NULL_LOC;
                    if ($superclass) {
                        inheritance_operator_loc = @superclass;
                        inheritance_operator_loc.end = inheritance_operator_loc.beg + 1;
                    }
                    $$ = NEW_CLASS($cpath, $bodystmt, $superclass, &@$, &@k_class, &inheritance_operator_loc, &@k_end);
                    nd_set_line(RNODE_CLASS($$)->nd_body, @k_end.end_pos.lineno);
                    nd_set_line($$, @superclass.end_pos.lineno);
                    local_pop(p);
                    p->ctxt.in_class = $k_class.in_class;
                    p->ctxt.cant_return = $k_class.cant_return;
                    p->ctxt.shareable_constant_value = $k_class.shareable_constant_value;
                }
            | k_class tLSHFT expr_value
                {
                    begin_definition("", &@k_class, &@tLSHFT);
                }
              term
              bodystmt
              k_end
                {
                    $$ = NEW_SCLASS($expr_value, $bodystmt, &@$, &@k_class, &@tLSHFT, &@k_end);
                    nd_set_line(RNODE_SCLASS($$)->nd_body, @k_end.end_pos.lineno);
                    set_line_body($bodystmt, nd_line($expr_value));
                    fixpos($$, $expr_value);
                    local_pop(p);
                    p->ctxt.in_def = $k_class.in_def;
                    p->ctxt.in_class = $k_class.in_class;
                    p->ctxt.cant_return = $k_class.cant_return;
                    p->ctxt.shareable_constant_value = $k_class.shareable_constant_value;
                }
            | k_module cpath
                {
                    begin_definition("module", &@k_module, &@cpath);
                }
              bodystmt
              k_end
                {
                    $$ = NEW_MODULE($cpath, $bodystmt, &@$, &@k_module, &@k_end);
                    nd_set_line(RNODE_MODULE($$)->nd_body, @k_end.end_pos.lineno);
                    nd_set_line($$, @cpath.end_pos.lineno);
                    local_pop(p);
                    p->ctxt.in_class = $k_module.in_class;
                    p->ctxt.cant_return = $k_module.cant_return;
                    p->ctxt.shareable_constant_value = $k_module.shareable_constant_value;
                }
            | defn_head[head]
              f_arglist[args]
                {
                    /* fork: claim the parameter parens before the body's
                     * calls can overwrite the pending slot */
                    pm_ydef_parens(p, (NODE *) $head->nd_def);
                }
              bodystmt
              k_end
                {
                    restore_defun(p, $head);
                    $$ = pm_ydef_finish(p, (NODE *) $head->nd_def, (NODE *) $args, $bodystmt, &@$, &@k_end);
                    local_pop(p);
                }
            | defs_head[head]
              f_arglist[args]
                {
                    /* fork: claim the parameter parens before the body's
                     * calls can overwrite the pending slot */
                    pm_ydef_parens(p, (NODE *) $head->nd_def);
                }
              bodystmt
              k_end
                {
                    restore_defun(p, $head);
                    $$ = pm_ydef_finish(p, (NODE *) $head->nd_def, (NODE *) $args, $bodystmt, &@$, &@k_end);
                    local_pop(p);
                }
            | keyword_break[kw]
                {
                    $$ = add_block_exit(p, NEW_BREAK(0, &@$, &@kw));
                }
            | keyword_next[kw]
                {
                    $$ = add_block_exit(p, NEW_NEXT(0, &@$, &@kw));
                }
            | keyword_redo[kw]
                {
                    $$ = add_block_exit(p, NEW_REDO(&@$, &@kw));
                }
            | keyword_retry[kw]
                {
                    if (!p->ctxt.in_defined) {
                        switch (p->ctxt.in_rescue) {
                          case before_rescue: yyerror1(&@kw, "Invalid retry without rescue"); break;
                          case after_rescue: /* ok */ break;
                          case after_else: yyerror1(&@kw, "Invalid retry after else"); break;
                          case after_ensure: yyerror1(&@kw, "Invalid retry after ensure"); break;
                        }
                    }
                    $$ = NEW_RETRY(&@$);
                }
            ;

primary_value	: value_expr(primary)
                ;

k_begin		: keyword_begin
                    {
                        token_info_push(p, "begin", &@$);
                    }
                ;

k_if		: keyword_if
                    {
                        WARN_EOL("if");
                        token_info_push(p, "if", &@$);
                        if (p->token_info && p->token_info->nonspc &&
                            p->token_info->next && !strcmp(p->token_info->next->token, "else")) {
                            const char *tok = p->lex.ptok - rb_strlen_lit("if");
                            const char *beg = p->lex.pbeg + p->token_info->next->beg.column;
                            beg += rb_strlen_lit("else");
                            while (beg < tok && ISSPACE(*beg)) beg++;
                            if (beg == tok) {
                                p->token_info->nonspc = 0;
                            }
                        }
                    }
                ;

k_unless	: keyword_unless
                    {
                        token_info_push(p, "unless", &@$);
                    }
                ;

k_while		: keyword_while[kw] allow_exits
                    {
                        $$ = $allow_exits;
                        token_info_push(p, "while", &@$);
                    }
                ;

k_until		: keyword_until[kw] allow_exits
                    {
                        $$ = $allow_exits;
                        token_info_push(p, "until", &@$);
                    }
                ;

k_case		: keyword_case
                    {
                        token_info_push(p, "case", &@$);
                    }
                ;

k_for		: keyword_for[kw] allow_exits
                    {
                        $$ = $allow_exits;
                        token_info_push(p, "for", &@$);
                    }
                ;

k_class		: keyword_class
                    {
                        token_info_push(p, "class", &@$);
                        $$ = p->ctxt;
                        p->ctxt.in_rescue = before_rescue;
                    }
                ;

k_module	: keyword_module
                    {
                        token_info_push(p, "module", &@$);
                        $$ = p->ctxt;
                        p->ctxt.in_rescue = before_rescue;
                    }
                ;

k_def		: keyword_def
                    {
                        token_info_push(p, "def", &@$);
                        $$ = NEW_DEF_TEMP(&@$);
                        p->ctxt.in_argdef = 1;
                    }
                ;

k_do		: keyword_do
                    {
                        token_info_push(p, "do", &@$);
                    }
                ;

k_do_block	: keyword_do_block
                    {
                        token_info_push(p, "do", &@$);
                    }
                ;

k_rescue	: keyword_rescue
                    {
                        token_info_warn(p, "rescue", p->token_info, 1, &@$);
                        $$ = p->ctxt;
                        p->ctxt.in_rescue = after_rescue;
                    }
                ;

k_ensure	: keyword_ensure
                    {
                        token_info_warn(p, "ensure", p->token_info, 1, &@$);
                        $$ = p->ctxt;
                    }
                ;

k_when		: keyword_when
                    {
                        token_info_warn(p, "when", p->token_info, 0, &@$);
                    }
                ;

k_else		: keyword_else
                    {
                        token_info *ptinfo_beg = p->token_info;
                        int same = ptinfo_beg && strcmp(ptinfo_beg->token, "case") != 0;
                        token_info_warn(p, "else", p->token_info, same, &@$);
                        if (same) {
                            token_info e;
                            e.next = ptinfo_beg->next;
                            e.token = "else";
                            token_info_setup(&e, p->lex.pbeg, &@$);
                            if (!e.nonspc) *ptinfo_beg = e;
                        }
                    }
                ;

k_elsif 	: keyword_elsif
                    {
                        WARN_EOL("elsif");
                        token_info_warn(p, "elsif", p->token_info, 1, &@$);
                    }
                ;

k_end		: keyword_end
                    {
                        token_info_pop(p, "end", &@$);
                        pop_end_expect_token_locations(p);
                    }
                | tDUMNY_END
                    {
                        compile_error(p, "syntax error, unexpected end-of-input");
                    }
                ;

k_return	: keyword_return
                    {
                        if (p->ctxt.cant_return && !dyna_in_block(p))
                            yyerror1(&@1, "Invalid return in class/module body");
                    }
                ;

k_yield 	: keyword_yield
                    {
                        if (!p->ctxt.in_defined && !p->ctxt.in_def && !compile_for_eval)
                            yyerror1(&@1, "Invalid yield");
                    }
                ;

then		: term
                | keyword_then
                | term keyword_then
                ;

do		: term
                | keyword_do_cond { $$ = keyword_do_cond; p->ydo.loc = @1; p->ydo.set = 1; }
                ;

if_tail		: opt_else
                | k_elsif expr_value then
                  compstmt(stmts)
                  if_tail
                    {
                        $$ = new_if(p, $2, $4, $5, &@$, &@1, &@3, &NULL_LOC);
                        fixpos($$, $2);
                    }
                ;

opt_else	: none
                | k_else compstmt(stmts)
                    {
                        $$ = pm_yelse(p, $2, &@1, &@$);
                    }
                ;

for_var		: lhs
                | mlhs
                ;

f_marg		: f_norm_arg
                    {
                        $$ = assignable(p, $1, 0, &@$);
                        mark_lvar_used(p, $$);
                    }
                | tLPAREN f_margs rparen
                    {
                        $$ = (NODE *)$2;
                    }
                ;


f_margs		: mlhs_items(f_marg)
                    {
                        $$ = NEW_MASGN($1, 0, &@$);
                    }
                | mlhs_items(f_marg) ',' f_rest_marg
                    {
                        $$ = NEW_MASGN($1, $3, &@$);
                    }
                | mlhs_items(f_marg) ',' f_rest_marg ',' mlhs_items(f_marg)
                    {
                        $$ = NEW_MASGN($1, NEW_POSTARG($3, $5, &@$), &@$);
                    }
                | f_rest_marg
                    {
                        $$ = NEW_MASGN(0, $1, &@$);
                    }
                | f_rest_marg ',' mlhs_items(f_marg)
                    {
                        $$ = NEW_MASGN(0, NEW_POSTARG($1, $3, &@$), &@$);
                    }
                ;

f_rest_marg	: tSTAR f_norm_arg
                    {
                        $$ = assignable(p, $2, 0, &@$);
                        mark_lvar_used(p, $$);
                    }
                | tSTAR
                    {
                        $$ = NODE_SPECIAL_NO_NAME_REST;
                    }
                ;

f_any_kwrest	: f_kwrest
                | f_no_kwarg
                    {
                        $$ = idNil;
                    }
                ;

f_eq		: {p->ctxt.in_argdef = 0;} '=';

block_args_tail	: args_tail_basic(primary_value, none)
                ;

excessed_comma	: ','
                    {
                        /* magic number for rest_id in iseq_set_arguments() */
                        $$ = NODE_SPECIAL_EXCESSIVE_COMMA;
                    }
                ;

block_param	: args-list(primary_value, opt_args_tail(block_args_tail, none))
                | f_arg[pre] excessed_comma
                    {
                        $$ = new_empty_args_tail(p, &@excessed_comma);
                        $$ = new_args(p, $pre, 0, $excessed_comma, 0, $$, &@$);
                    }
                | f_arg[pre] opt_args_tail(block_args_tail, none)[tail]
                    {
                        $$ = new_args(p, $pre, 0, 0, 0, $tail, &@$);
                    }
                | tail-only-args(block_args_tail)
                ;

opt_block_param_def	: none
                    | block_param_def
                        {
                            p->command_start = TRUE;
                        }
                    ;

block_param_def	: '|' opt_block_param opt_bv_decl '|'
                    {
                        p->max_numparam = ORDINAL_PARAM;
                        p->ctxt.in_argdef = 0;
                        $$ = pm_yblock_params(p, (NODE *) $2, NULL, &@1, &@4);
                    }
                ;

opt_block_param	: /* none */
                    {
                        $$ = 0;
                    }
                | block_param
                ;

opt_bv_decl	: '\n'?
                    {
                        $$ = 0;
                    }
                | '\n'? ';' bv_decls '\n'?
                    {
                        $$ = 0;
                    }
                ;

bv_decls	: bvar
                | bv_decls ',' bvar
                ;

bvar		: tIDENTIFIER
                    {
                        new_bv(p, $1);
                    }
                | f_bad_arg
                ;

max_numparam	:   {
                        $$ = p->max_numparam;
                        p->max_numparam = 0;
                    }
                ;

numparam	:   {
                        $$ = numparam_push(p);
                    }
                ;

it_id		:   {
                        $$ = p->it_id;
                        p->it_id = 0;
                    }
                ;

lambda		: tLAMBDA[lpar]
                    {
                        token_info_push(p, "->", &@lpar);
                        $$ = dyna_push(p);
                    }[dyna]<vars>
                  max_numparam numparam it_id allow_exits
                  f_larglist[args]
                    {
                        CMDARG_PUSH(0);
                    }
                  lambda_body[body]
                    {
                        int max_numparam = p->max_numparam;
                        ID it_id = p->it_id;
                        p->lex.lpar_beg = $lpar;
                        p->max_numparam = $max_numparam;
                        p->it_id = $it_id;
                        restore_block_exit(p, $allow_exits);
                        CMDARG_POP();
                        $args = args_with_numbered(p, $args, max_numparam, it_id);
                        {
                            YYLTYPE loc = code_loc_gen(&@lpar, &@body);
                            $$ = NEW_LAMBDA($args, $body->node, &loc, &@lpar, &$body->opening_loc, &$body->closing_loc);
                            nd_set_line(RNODE_LAMBDA($$)->nd_body, @body.end_pos.lineno);
                            nd_set_line($$, @args.end_pos.lineno);
                            xfree($body);
                        }
                        numparam_pop(p, $numparam);
                        dyna_pop(p, $dyna);
                    }
                ;

f_larglist	: '(' f_largs[args] opt_bv_decl ')'
                    {
                        p->ctxt.in_argdef = 0;
                        $$ = (rb_node_args_t *) pm_yblock_params(p, (NODE *) $args, NULL /* PORTME: $opt_bv_decl */, &@1, &@4);
                        p->max_numparam = ORDINAL_PARAM;
                    }
                | f_largs[args]
                    {
                        p->ctxt.in_argdef = 0;
                        if (0) /* PORTME: args_info_empty_p on the ported parameter builder */
                            p->max_numparam = ORDINAL_PARAM;
                        $$ = (rb_node_args_t *) pm_yblock_params(p, (NODE *) $args, NULL, NULL, NULL);
                    }
                ;

lambda_body	: tLAMBEG compstmt(stmts) '}'
                    {
                        token_info_pop(p, "}", &@3);
                        $$ = new_locations_lambda_body(p, $2, &@2, &@1, &@3);
                    }
                | keyword_do_LAMBDA
                    {
                    }
                  bodystmt k_end
                    {
                        $$ = new_locations_lambda_body(p, $3, &@3, &@1, &@4);
                    }
                ;

do_block	: k_do_block do_body k_end
                    {
                        $$ = $2;
                        set_embraced_location($$, &@1, &@3);
                    }
                ;

block_call	: command do_block
                    {
                        $$ = command_add_block(p, $1, $2, &@$);
                        fixpos($$, $1);
                    }
                | block_call call_op2 operation2 opt_paren_args
                    {
                        bool has_args = $4 != 0;
                        if (NODE_EMPTY_ARGS_P($4)) $4 = 0;
                        $$ = new_qcall(p, $2, $1, $3, $4, &@3, &@$);
                        if (has_args) {
                        }
                    }
                | block_call call_op2 operation2 opt_paren_args brace_block
                    {
                        if (NODE_EMPTY_ARGS_P($4)) $4 = 0;
                        $$ = new_command_qcall(p, $2, $1, $3, $4, $5, &@3, &@$);
                    }
                | block_call call_op2 operation2 command_args do_block
                    {
                        $$ = new_command_qcall(p, $2, $1, $3, $4, $5, &@3, &@$);
                    }
                | block_call call_op2 paren_args
                    {
                        $$ = new_qcall(p, $2, $1, idCall, $3, &@2, &@$);
                        nd_set_line($$, @2.end_pos.lineno);
                    }
                ;

method_call	: fcall paren_args
                    {
                        $$ = pm_yfcall_args(p, (NODE *)$1, $2, &@$);
                    }
                | primary_value call_op operation2 opt_paren_args
                    {
                        bool has_args = $4 != 0;
                        if (NODE_EMPTY_ARGS_P($4)) $4 = 0;
                        $$ = new_qcall(p, $2, $1, $3, $4, &@3, &@$);
                        nd_set_line($$, @3.end_pos.lineno);
                        if (has_args) {
                        }
                    }
                | primary_value tCOLON2 operation2 paren_args
                    {
                        $$ = new_qcall(p, idCOLON2, $1, $3, $4, &@3, &@$);
                        nd_set_line($$, @3.end_pos.lineno);
                    }
                | primary_value tCOLON2 operation3
                    {
                        $$ = new_qcall(p, idCOLON2, $1, $3, 0, &@3, &@$);
                    }
                | primary_value call_op2 paren_args
                    {
                        $$ = new_qcall(p, $2, $1, idCall, $3, &@2, &@$);
                        nd_set_line($$, @2.end_pos.lineno);
                    }
                | keyword_super paren_args
                    {
                        rb_code_location_t lparen_loc = @2;
                        rb_code_location_t rparen_loc = @2;
                        lparen_loc.end = lparen_loc.beg + 1;
                        rparen_loc.beg = rparen_loc.end - 1;
                        /* the constructor takes these directly; drop the
                         * pending slot paren_args filled */
                        p->yparens.set = 0;

                        $$ = NEW_SUPER($2, &@$, &@1, &lparen_loc, &rparen_loc);
                    }
                | keyword_super
                    {
                        $$ = NEW_ZSUPER(&@$);
                    }
                | primary_value '[' opt_call_args rbracket
                    {
                        $$ = NEW_CALL($1, tAREF, $3, &@$);
                        $$ = pm_yindex_call(p, $$, &@2, &@4);
                        fixpos($$, $1);
                    }
                ;

brace_block	: '{' brace_body '}'
                    {
                        $$ = $2;
                        set_embraced_location($$, &@1, &@3);
                    }
                | k_do do_body k_end
                    {
                        $$ = $2;
                        set_embraced_location($$, &@1, &@3);
                    }
                ;

brace_body	: {$$ = dyna_push(p);}[dyna]<vars>
                  max_numparam numparam it_id allow_exits
                  opt_block_param_def[args] compstmt(stmts)
                    {
                        int max_numparam = p->max_numparam;
                        ID it_id = p->it_id;
                        p->max_numparam = $max_numparam;
                        p->it_id = $it_id;
                        $args = args_with_numbered(p, $args, max_numparam, it_id);
                        $$ = NEW_ITER($args, $compstmt, &@$);
                        restore_block_exit(p, $allow_exits);
                        numparam_pop(p, $numparam);
                        dyna_pop(p, $dyna);
                    }
                ;

do_body 	:   {
                        $$ = dyna_push(p);
                        CMDARG_PUSH(0);
                    }[dyna]<vars>
                  max_numparam numparam it_id allow_exits
                  opt_block_param_def[args] bodystmt
                    {
                        int max_numparam = p->max_numparam;
                        ID it_id = p->it_id;
                        p->max_numparam = $max_numparam;
                        p->it_id = $it_id;
                        $args = args_with_numbered(p, $args, max_numparam, it_id);
                        $$ = NEW_ITER($args, $bodystmt, &@$);
                        CMDARG_POP();
                        restore_block_exit(p, $allow_exits);
                        numparam_pop(p, $numparam);
                        dyna_pop(p, $dyna);
                    }
                ;

case_args	: arg_value
                    {
                        check_literal_when(p, $arg_value, &@arg_value);
                        $$ = NEW_LIST($arg_value, &@$);
                    }
                | tSTAR arg_value
                    {
                        $$ = NEW_SPLAT($arg_value, &@$, &@tSTAR);
                    }
                | case_args[non_last_args] ',' arg_value
                    {
                        check_literal_when(p, $arg_value, &@arg_value);
                        $$ = last_arg_append(p, $non_last_args, $arg_value, &@$);
                    }
                | case_args[non_last_args] ',' tSTAR arg_value
                    {
                        $$ = rest_arg_append(p, $non_last_args, $arg_value, &@$);
                    }
                ;

case_body	: k_when case_args then
                  compstmt(stmts)
                  cases
                    {
                        $$ = NEW_WHEN($2, $4, $5, &@$, &@1, &@3);
                        fixpos($$, $2);
                    }
                ;

cases		: opt_else
                | case_body
                ;

p_pvtbl 	: {$$ = p->pvtbl; p->pvtbl = st_init_numtable();};
p_pktbl 	: {$$ = p->pktbl; p->pktbl = 0;};

p_in_kwarg	:   {
                        $$ = p->ctxt;
                        SET_LEX_STATE(EXPR_BEG|EXPR_LABEL);
                        p->command_start = FALSE;
                        p->ctxt.in_kwarg = 1;
                        p->ctxt.in_alt_pattern = 0;
                        p->ctxt.capture_in_pattern = 0;
                    }
                ;

p_case_body	: keyword_in
                  p_in_kwarg[ctxt] p_pvtbl p_pktbl
                  p_top_expr[expr] then
                    {
                        pop_pktbl(p, $p_pktbl);
                        pop_pvtbl(p, $p_pvtbl);
                        p->ctxt.in_kwarg = $ctxt.in_kwarg;
                        p->ctxt.in_alt_pattern = $ctxt.in_alt_pattern;
                        p->ctxt.capture_in_pattern = $ctxt.capture_in_pattern;
                    }
                  compstmt(stmts)
                  p_cases[cases]
                    {
                        $$ = NEW_IN($expr, $compstmt, $cases, &@$, &@keyword_in, &@then, &NULL_LOC);
                    }
                ;

p_cases 	: opt_else
                | p_case_body
                ;

p_top_expr	: p_top_expr_body
                | p_top_expr_body modifier_if expr_value
                    {
                        $$ = new_if(p, $3, $1, 0, &@$, &@2, &NULL_LOC, &NULL_LOC);
                        fixpos($$, $3);
                    }
                | p_top_expr_body modifier_unless expr_value
                    {
                        $$ = new_unless(p, $3, $1, 0, &@$, &@2, &NULL_LOC, &NULL_LOC);
                        fixpos($$, $3);
                    }
                ;

p_top_expr_body : p_expr
                | p_expr ','
                    {
                        $$ = new_array_pattern_tail(p, 0, 1, 0, 0, &@$);
                        $$ = new_array_pattern(p, 0, $1, $$, &@$);
                    }
                | p_expr ',' p_args
                    {
                        $$ = new_array_pattern(p, 0, $1, $3, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @1.beg_pos); */
                    }
                | p_find
                    {
                        $$ = new_find_pattern(p, 0, $1, &@$);
                    }
                | p_args_tail
                    {
                        $$ = new_array_pattern(p, 0, 0, $1, &@$);
                    }
                | p_kwargs
                    {
                        $$ = new_hash_pattern(p, 0, $1, &@$);
                    }
                ;

p_expr		: p_as
                ;

p_as		: p_expr tASSOC p_variable
                    {
                        NODE *n = NEW_LIST($1, &@$);
                        n = list_append(p, n, $3);
                        $$ = new_hash(p, n, &@$);
                    }
                | p_alt
                ;

p_alt		: p_alt[left] '|'[alt]
                    {
                        p->ctxt.in_alt_pattern = 1;
                    }
                  p_expr_basic[right]
                    {
                        if (p->ctxt.capture_in_pattern) {
                            yyerror1(&@alt, "alternative pattern after variable capture");
                        }
                        p->ctxt.in_alt_pattern = 0;
                        $$ = NEW_OR($left, $right, &@$, &@alt);
                    }
                | p_expr_basic
                ;

p_lparen	: '(' p_pktbl
                    {
                        $$ = $2;
                    }
                ;

p_lbracket	: '[' p_pktbl
                    {
                        $$ = $2;
                    }
                ;

p_expr_basic	: p_value
                | p_variable
                | p_const p_lparen[p_pktbl] p_args rparen
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = new_array_pattern(p, $p_const, 0, $p_args, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @p_const.beg_pos); */
                    }
                | p_const p_lparen[p_pktbl] p_find rparen
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = new_find_pattern(p, $p_const, $p_find, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @p_const.beg_pos); */
                    }
                | p_const p_lparen[p_pktbl] p_kwargs rparen
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = new_hash_pattern(p, $p_const, $p_kwargs, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @p_const.beg_pos); */
                    }
                | p_const '(' rparen
                    {
                        $$ = new_array_pattern_tail(p, 0, 0, 0, 0, &@$);
                        $$ = new_array_pattern(p, $p_const, 0, $$, &@$);
                    }
                | p_const p_lbracket[p_pktbl] p_args rbracket
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = new_array_pattern(p, $p_const, 0, $p_args, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @p_const.beg_pos); */
                    }
                | p_const p_lbracket[p_pktbl] p_find rbracket
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = new_find_pattern(p, $p_const, $p_find, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @p_const.beg_pos); */
                    }
                | p_const p_lbracket[p_pktbl] p_kwargs rbracket
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = new_hash_pattern(p, $p_const, $p_kwargs, &@$);
                        YSTUB("grammar"); /* PORTME: nd_set_first_loc($$, @p_const.beg_pos); */
                    }
                | p_const '[' rbracket
                    {
                        $$ = new_array_pattern_tail(p, 0, 0, 0, 0, &@$);
                        $$ = new_array_pattern(p, $p_const, 0, $$, &@$);
                    }
                | tLBRACK p_args rbracket
                    {
                        $$ = new_array_pattern(p, 0, 0, $p_args, &@$);
                    }
                | tLBRACK p_find rbracket
                    {
                        $$ = new_find_pattern(p, 0, $p_find, &@$);
                    }
                | tLBRACK rbracket
                    {
                        $$ = new_array_pattern_tail(p, 0, 0, 0, 0, &@$);
                        $$ = new_array_pattern(p, 0, 0, $$, &@$);
                    }
                | tLBRACE p_pktbl lex_ctxt[ctxt]
                    {
                        p->ctxt.in_kwarg = 0;
                    }
                  p_kwargs rbrace
                    {
                        pop_pktbl(p, $p_pktbl);
                        p->ctxt.in_kwarg = $ctxt.in_kwarg;
                        $$ = new_hash_pattern(p, 0, $p_kwargs, &@$);
                    }
                | tLBRACE rbrace
                    {
                        $$ = new_hash_pattern_tail(p, 0, 0, &@$);
                        $$ = new_hash_pattern(p, 0, $$, &@$);
                    }
                | tLPAREN p_pktbl p_expr rparen
                    {
                        pop_pktbl(p, $p_pktbl);
                        $$ = $p_expr;
                    }
                ;

p_args		: p_expr
                    {
                        NODE *pre_args = NEW_LIST($1, &@$);
                        $$ = new_array_pattern_tail(p, pre_args, 0, 0, 0, &@$);
                    }
                | p_args_head
                    {
                        $$ = new_array_pattern_tail(p, $1, 1, 0, 0, &@$);
                    }
                | p_args_head p_arg
                    {
                        $$ = new_array_pattern_tail(p, list_concat(p, $1, $2), 0, 0, 0, &@$);
                    }
                | p_args_head p_rest
                    {
                        $$ = new_array_pattern_tail(p, $1, 1, $2, 0, &@$);
                    }
                | p_args_head p_rest ',' p_args_post
                    {
                        $$ = new_array_pattern_tail(p, $1, 1, $2, $4, &@$);
                    }
                | p_args_tail
                ;

p_args_head	: p_arg ','
                | p_args_head p_arg ','
                    {
                        $$ = list_concat(p, $1, $2);
                    }
                ;

p_args_tail	: p_rest
                    {
                        $$ = new_array_pattern_tail(p, 0, 1, $1, 0, &@$);
                    }
                | p_rest ',' p_args_post
                    {
                        $$ = new_array_pattern_tail(p, 0, 1, $1, $3, &@$);
                    }
                ;

p_find		: p_rest ',' p_args_post ',' p_rest
                    {
                        $$ = new_find_pattern_tail(p, $1, $3, $5, &@$);
                    }
                ;


p_rest		: tSTAR tIDENTIFIER
                    {
                        error_duplicate_pattern_variable(p, $2, &@2);
                        $$ = assignable(p, $2, 0, &@$);
                    }
                | tSTAR
                    {
                        $$ = 0;
                    }
                ;

p_args_post	: p_arg
                | p_args_post ',' p_arg
                    {
                        $$ = list_concat(p, $1, $3);
                    }
                ;

p_arg		: p_expr
                    {
                        $$ = NEW_LIST($1, &@$);
                    }
                ;

p_kwargs	: p_kwarg ',' p_any_kwrest
                    {
                        $$ =  new_hash_pattern_tail(p, new_unique_key_hash(p, $1, &@$), $3, &@$);
                    }
                | p_kwarg
                    {
                        $$ =  new_hash_pattern_tail(p, new_unique_key_hash(p, $1, &@$), 0, &@$);
                    }
                | p_kwarg ','
                    {
                        $$ =  new_hash_pattern_tail(p, new_unique_key_hash(p, $1, &@$), 0, &@$);
                    }
                | p_any_kwrest
                    {
                        $$ =  new_hash_pattern_tail(p, new_hash(p, 0, &@$), $1, &@$);
                    }
                ;

p_kwarg 	: p_kw
                | p_kwarg ',' p_kw
                    {
                        $$ = list_concat(p, $1, $3);
                    }
                ;

p_kw		: p_kw_label p_expr
                    {
                        error_duplicate_pattern_key(p, $1, &@1);
                        $$ = list_append(p, NEW_LIST(NEW_SYM(rb_id2str($1), &@1), &@$), $2);
                    }
                | p_kw_label
                    {
                        error_duplicate_pattern_key(p, $1, &@1);
                        if ($1 && !is_local_id($1)) {
                            yyerror1(&@1, "key must be valid as local variables");
                        }
                        error_duplicate_pattern_variable(p, $1, &@1);
                        $$ = list_append(p, NEW_LIST(NEW_SYM(rb_id2str($1), &@$), &@$), assignable(p, $1, 0, &@$));
                    }
                ;

p_kw_label	: tLABEL
                | tSTRING_BEG string_contents tLABEL_END
                    {
                        YYLTYPE loc = code_loc_gen(&@1, &@3);
                        if (!$2 || nd_type_p($2, NODE_STR)) {
                            NODE *node = dsym_node(p, $2, &loc);
                            $$ = rb_sym2id(rb_node_sym_string_val(node));
                        }
                        else {
                            yyerror1(&loc, "symbol literal with interpolation is not allowed");
                            $$ = rb_intern_str(STR_NEW0());
                        }
                    }
                ;

p_kwrest	: kwrest_mark tIDENTIFIER
                    {
                        $$ = $2;
                    }
                | kwrest_mark
                    {
                        $$ = 0;
                    }
                ;

p_kwnorest	: kwrest_mark keyword_nil
                    {
                        $$ = 0;
                    }
                ;

p_any_kwrest	: p_kwrest
                | p_kwnorest
                    {
                        $$ = idNil;
                    }
                ;

p_value 	: p_primitive
                | range_expr(p_primitive)
                | p_var_ref
                | p_expr_ref
                | p_const
                ;

p_primitive	: inline_primary
                | keyword_variable
                    {
                        if (!($$ = gettable(p, $1, &@$))) $$ = NEW_ERROR(&@$);
                    }
                | lambda
                ;

p_variable	: tIDENTIFIER
                    {
                        error_duplicate_pattern_variable(p, $1, &@1);
                        $$ = assignable(p, $1, 0, &@$);
                    }
                ;

p_var_ref	: '^' tIDENTIFIER
                    {
                        NODE *n = gettable(p, $2, &@$);
                        if (!n) {
                            n = NEW_ERROR(&@$);
                        }
                        else if (!(nd_type_p(n, NODE_LVAR) || nd_type_p(n, NODE_DVAR))) {
                            compile_error(p, "%"PRIsVALUE": no such local variable", rb_id2str($2));
                        }
                        $$ = n;
                    }
                | '^' nonlocal_var
                    {
                        if (!($$ = gettable(p, $2, &@$))) $$ = NEW_ERROR(&@$);
                    }
                ;

p_expr_ref	: '^' tLPAREN expr_value rparen
                    {
                        $$ = NEW_BLOCK($3, &@$);
                    }
                ;

p_const 	: tCOLON3 cname
                    {
                        $$ = NEW_COLON3($2, &@$, &@1, &@2);
                    }
                | p_const tCOLON2 cname
                    {
                        $$ = NEW_COLON2($1, $3, &@$, &@2, &@3);
                    }
                | tCONSTANT
                   {
                        $$ = gettable(p, $1, &@$);
                   }
                ;

opt_rescue	: k_rescue exc_list exc_var then
                  compstmt(stmts)
                  opt_rescue
                    {
                        $$ = NEW_RESBODY($2, pm_ytarget(p, $3), $5, $6, &@$);
                        $$ = pm_yrescue_finish(p, $$, &@1, &@4);
                    }
                | none
                ;

exc_list	: arg_value
                    {
                        $$ = NEW_LIST($1, &@$);
                    }
                | mrhs
                    {
                        if (!($$ = splat_array($1))) $$ = $1;
                    }
                | none
                ;

exc_var		: tASSOC lhs
                    {
                        $$ = $2;
                    }
                | none
                ;

opt_ensure	: k_ensure stmts terms?
                    {
                        p->ctxt.in_rescue = $1.in_rescue;
                        void_expr(p, void_stmts(p, $2));
                        $$ = pm_yensure(p, $2, &@1, &@$);
                    }
                | none
                ;

literal		: numeric
                | symbol
                ;

strings		: string
                    {
                        if (!$1) {
                            $$ = NEW_STR(STRING_NEW0(), &@$);
                        }
                        else {
                            $$ = evstr2dstr(p, $1);
                        }
                    }
                ;

string		: tCHAR
                | string1
                | string string1
                    {
                        $$ = literal_concat(p, $1, $2, &@$);
                    }
                ;

string1		: tSTRING_BEG string_contents tSTRING_END
                    {
                        $$ = heredoc_dedent(p, $2);
                        $$ = string_literal_quotes(p, $$, &@1, &@3, &@$);
                        if (p->heredoc_indent > 0) {
                            p->heredoc_indent = 0;
                        }
                    }
                ;

xstring		: tXSTRING_BEG xstring_contents tSTRING_END
                    {
                        $$ = new_xstring(p, heredoc_dedent(p, $2), &@$);
                        if (p->heredoc_indent > 0) {
                            p->heredoc_indent = 0;
                        }
                    }
                ;

regexp		: tREGEXP_BEG regexp_contents tREGEXP_END
                    {
                        $$ = new_regexp(p, $2, $3, &@$, &@1, &@2, &@3);
                    }
                ;

words		: words(tWORDS_BEG, word_list)
                ;

word_list	: /* none */
                    {
                        $$ = 0;
                    }
                | word_list word ' '+
                    {
                        $$ = list_append(p, $1, evstr2dstr(p, $2));
                    }
                ;

word		: string_content
                | word string_content
                    {
                        $$ = literal_concat(p, $1, $2, &@$);
                    }
                ;

symbols 	: words(tSYMBOLS_BEG, symbol_list)
                ;

symbol_list	: /* none */
                    {
                        $$ = 0;
                    }
                | symbol_list word ' '+
                    {
                        $$ = symbol_append(p, $1, evstr2dstr(p, $2));
                    }
                ;

qwords		: words(tQWORDS_BEG, qword_list)
                ;

qsymbols	: words(tQSYMBOLS_BEG, qsym_list)
                ;

qword_list	: /* none */
                    {
                        $$ = 0;
                    }
                | qword_list tSTRING_CONTENT ' '+
                    {
                        $$ = list_append(p, $1, $2);
                    }
                ;

qsym_list	: /* none */
                    {
                        $$ = 0;
                    }
                | qsym_list tSTRING_CONTENT ' '+
                    {
                        $$ = symbol_append(p, $1, $2);
                    }
                ;

string_contents	: /* none */
                    {
                        $$ = 0;
                    }
                | string_contents string_content
                    {
                        $$ = literal_concat(p, $1, $2, &@$);
                    }
                ;

xstring_contents: /* none */
                    {
                        $$ = 0;
                    }
                | xstring_contents string_content
                    {
                        $$ = literal_concat(p, $1, $2, &@$);
                    }
                ;

regexp_contents	: /* none */
                    {
                        $$ = 0;
                    }
                | regexp_contents string_content
                    {
                        NODE *head = $1, *tail = $2;
                        if (!head) {
                            $$ = tail;
                        }
                        else if (!tail) {
                            $$ = head;
                        }
                        else {
                            switch (nd_type(head)) {
                              case NODE_STR:
                                head = str2dstr(p, head);
                                break;
                              case NODE_DSTR:
                                break;
                              default:
                                head = list_append(p, NEW_DSTR(0, &@$), head);
                                break;
                            }
                            $$ = list_append(p, head, tail);
                        }
                    }
                ;

string_content	: tSTRING_CONTENT[content]
                | tSTRING_DVAR[state]
                    {
                        /* need to backup p->lex.strterm so that a string literal `%&foo,#$&,bar&` can be parsed */
                        $$ = p->lex.strterm;
                        p->lex.strterm = 0;
                        SET_LEX_STATE(EXPR_BEG);
                    }[strterm]<strterm>
                  string_dvar[dvar]
                    {
                        p->lex.strterm = $strterm;
                        $$ = NEW_EVSTR($dvar, &@$, &@state, &NULL_LOC);
                        nd_set_line($$, @dvar.end_pos.lineno);
                    }
                | tSTRING_DBEG[state]
                    {
                        CMDARG_PUSH(0);
                        COND_PUSH(0);
                        /* need to backup p->lex.strterm so that a string literal `%!foo,#{ !0 },bar!` can be parsed */
                        $$ = p->lex.strterm;
                        p->lex.strterm = 0;
                        SET_LEX_STATE(EXPR_BEG);
                    }[term]<strterm>
                    {
                        $$ = p->lex.brace_nest;
                        p->lex.brace_nest = 0;
                    }[brace]<num>
                    {
                        $$ = p->lex.lpar_beg;
                        p->lex.lpar_beg = -1;
                    }[lpar]<num>
                    {
                        $$ = p->heredoc_indent;
                        p->heredoc_indent = 0;
                    }[indent]<num>
                  compstmt(stmts) string_dend
                    {
                        COND_POP();
                        CMDARG_POP();
                        p->lex.strterm = $term;
                        SET_LEX_STATE($state);
                        p->lex.brace_nest = $brace;
                        p->lex.lpar_beg = $lpar;
                        p->heredoc_indent = $indent;
                        p->heredoc_line_indent = -1;
                        if ($compstmt) nd_unset_fl_newline($compstmt);
                        $$ = new_evstr(p, $compstmt, &@$, &@state, &@string_dend);
                    }
                ;

string_dend	: tSTRING_DEND
                | END_OF_INPUT
                ;

string_dvar	: nonlocal_var
                    {
                        if (!($$ = gettable(p, $1, &@$))) $$ = NEW_ERROR(&@$);
                    }
                | backref
                ;

symbol		: ssym
                | dsym
                ;

ssym		: tSYMBEG sym
                    {
                        SET_LEX_STATE(EXPR_END);
                        rb_parser_string_t *str = rb_id2str($2);
                        /*
                         * TODO:
                         *   set_yylval_noname sets invalid id to yylval.
                         *   This branch can be removed once yylval is changed to
                         *   hold lexed string.
                         */
                        if (!str) str = STR_NEW0();
                        $$ = NEW_SYM(str, &@$);
                    }
                ;

sym		: fname
                | nonlocal_var
                ;

dsym		: tSYMBEG string_contents tSTRING_END
                    {
                        SET_LEX_STATE(EXPR_END);
                        $$ = dsym_node(p, $2, &@$);
                    }
                ;

numeric 	: simple_numeric
                | tUMINUS_NUM simple_numeric   %prec tLOWEST
                    {
                        $$ = $2;
                        negate_lit(p, $$, &@$);
                    }
                ;

simple_numeric	: tINTEGER
                | tFLOAT
                | tRATIONAL
                | tIMAGINARY
                ;

nonlocal_var	: tIVAR
                | tGVAR
                | tCVAR
                ;

user_variable	: ident_or_const
                | nonlocal_var
                ;

keyword_variable: keyword_nil {$$ = KWD2EID(nil, $1);}
                | keyword_self {$$ = KWD2EID(self, $1);}
                | keyword_true {$$ = KWD2EID(true, $1);}
                | keyword_false {$$ = KWD2EID(false, $1);}
                | keyword__FILE__ {$$ = KWD2EID(_FILE__, $1);}
                | keyword__LINE__ {$$ = KWD2EID(_LINE__, $1);}
                | keyword__ENCODING__ {$$ = KWD2EID(_ENCODING__, $1);}
                ;

var_ref		: user_variable
                    {
                        if (!($$ = gettable(p, $1, &@$))) $$ = NEW_ERROR(&@$);
                        if (ifdef_ripper(id_is_var(p, $1), false)) {
                        }
                        else {
                        }
                    }
                | keyword_variable
                    {
                        if (!($$ = gettable(p, $1, &@$))) $$ = NEW_ERROR(&@$);
                    }
                ;

var_lhs		: user_or_keyword_variable
                    {
                        $$ = assignable(p, $1, 0, &@$);
                    }
                ;

backref		: tNTH_REF
                | tBACK_REF
                ;

superclass	: '<'
                    {
                        SET_LEX_STATE(EXPR_BEG);
                        p->command_start = TRUE;
                    }
                  expr_value term
                    {
                        $$ = $3;
                    }
                | none
                ;

f_opt_paren_args: f_paren_args
                | f_empty_arg
                    {
                        p->ctxt.in_argdef = 0;
                    }
                ;

f_empty_arg	: /* none */
                    {
                        $$ = new_empty_args_tail(p, &@$);
                        $$ = new_args(p, 0, 0, 0, 0, $$, &@$);
                    }
                ;

f_paren_args	: '(' f_args rparen
                    {
                        $$ = $2;
                        pm_yparens_set(p, &@1, &@3);
                        SET_LEX_STATE(EXPR_BEG);
                        p->command_start = TRUE;
                        p->ctxt.in_argdef = 0;
                    }
                ;

f_arglist	: f_paren_args
                |   {
                        $$ = p->ctxt;
                        p->ctxt.in_kwarg = 1;
                        p->ctxt.in_argdef = 1;
                        SET_LEX_STATE(p->lex.state|EXPR_LABEL); /* force for args */
                    }<ctxt>
                  f_args term
                    {
                        p->ctxt.in_kwarg = $1.in_kwarg;
                        p->ctxt.in_argdef = 0;
                        $$ = $2;
                        SET_LEX_STATE(EXPR_BEG);
                        p->command_start = TRUE;
                    }
                ;

args_tail	: args_tail_basic(arg_value, opt_comma)
                | args_forward
                    {
                        add_forwarding_args(p);
                        $$ = new_args_tail(p, 0, $args_forward, arg_FWD_BLOCK, &@args_forward);
                        YSTUB("grammar"); /* PORTME: $$->nd_ainfo.forwarding = 1; */
                    }
                ;

largs_tail	: args_tail_basic(arg_value, none)
                | args_forward
                    {
                        yyerror1(&@args_forward, "unexpected ... in lambda argument");
                        $$ = new_args_tail(p, 0, 0, 0, &@args_forward);
                        YSTUB("grammar"); /* PORTME: $$->nd_ainfo.forwarding = 1; */
                    }
                ;

%rule args-list(value, tail) <node_args>
                : f_arg[pre] ',' f_opt_arg(value)[opt] ',' f_rest_arg[rest] tail
                    {
                        $$ = new_args(p, $pre, $opt, $rest, 0, $tail, &@$);
                    }
                | f_arg[pre] ',' f_opt_arg(value)[opt] ',' f_rest_arg[rest] ',' f_arg[post] tail
                    {
                        $$ = new_args(p, $pre, $opt, $rest, $post, $tail, &@$);
                    }
                | f_arg[pre] ',' f_opt_arg(value)[opt] tail
                    {
                        $$ = new_args(p, $pre, $opt, 0, 0, $tail, &@$);
                    }
                | f_arg[pre] ',' f_opt_arg(value)[opt] ',' f_arg[post] tail
                    {
                        $$ = new_args(p, $pre, $opt, 0, $post, $tail, &@$);
                    }
                | f_arg[pre] ',' f_rest_arg[rest] tail
                    {
                        $$ = new_args(p, $pre, 0, $rest, 0, $tail, &@$);
                    }
                | f_arg[pre] ',' f_rest_arg[rest] ',' f_arg[post] tail
                    {
                        $$ = new_args(p, $pre, 0, $rest, $post, $tail, &@$);
                    }
                | f_opt_arg(value)[opt] ',' f_rest_arg[rest] tail
                    {
                        $$ = new_args(p, 0, $opt, $rest, 0, $tail, &@$);
                    }
                | f_opt_arg(value)[opt] ',' f_rest_arg[rest] ',' f_arg[post] tail
                    {
                        $$ = new_args(p, 0, $opt, $rest, $post, $tail, &@$);
                    }
                | f_opt_arg(value)[opt] tail
                    {
                        $$ = new_args(p, 0, $opt, 0, 0, $tail, &@$);
                    }
                | f_opt_arg(value)[opt] ',' f_arg[post] tail
                    {
                        $$ = new_args(p, 0, $opt, 0, $post, $tail, &@$);
                    }
                | f_rest_arg[rest] tail
                    {
                        $$ = new_args(p, 0, 0, $rest, 0, $tail, &@$);
                    }
                | f_rest_arg[rest] ',' f_arg[post] tail
                    {
                        $$ = new_args(p, 0, 0, $rest, $post, $tail, &@$);
                    }
                ;

%rule tail-only-args(tail) <node_args>
                : tail
                    {
                        $$ = new_args(p, 0, 0, 0, 0, $tail, &@$);
                    }
                ;

%rule f_args-list(tail, trailing) <node_args>
                : args-list(arg_value, opt_args_tail(tail, trailing))
                | f_arg[pre] opt_args_tail(tail, trailing)[tail]
                    {
                        $$ = new_args(p, $pre, 0, 0, 0, $tail, &@$);
                    }
                | tail-only-args(tail)
                | f_empty_arg
                ;

f_args		: f_args-list(args_tail, opt_comma)
                ;

f_largs		: f_args-list(largs_tail, none)
                ;

args_forward	: tBDOT3
                    {
                        $$ = idFWD_KWREST;
                    }
                ;

f_bad_arg	: tCONSTANT
                    {
                        static const char mesg[] = "formal argument cannot be a constant";
                        yyerror1(&@1, mesg);
                        $$ = 0;
                    }
                | tIVAR
                    {
                        static const char mesg[] = "formal argument cannot be an instance variable";
                        yyerror1(&@1, mesg);
                        $$ = 0;
                    }
                | tGVAR
                    {
                        static const char mesg[] = "formal argument cannot be a global variable";
                        yyerror1(&@1, mesg);
                        $$ = 0;
                    }
                | tCVAR
                    {
                        static const char mesg[] = "formal argument cannot be a class variable";
                        yyerror1(&@1, mesg);
                        $$ = 0;
                    }
                ;

f_norm_arg	: f_bad_arg
                | tIDENTIFIER
                    {
                        VALUE e = formal_argument_error(p, $$ = $1);
                        if (e) {
                        }
                        p->max_numparam = ORDINAL_PARAM;
                    }
                ;

f_arg_asgn	: f_norm_arg
                    {
                        arg_var(p, $1);
                        $$ = $1;
                    }
                ;

f_arg_item	: f_arg_asgn
                    {
                        $$ = NEW_ARGS_AUX($1, 1, &@1);
                    }
                | tLPAREN f_margs rparen
                    {
                        ID tid = internal_id(p);
                        YYLTYPE loc;
                        YSTUB("grammar"); /* PORTME: loc.beg_pos = @2.beg_pos; */
                        YSTUB("grammar"); /* PORTME: loc.end_pos = @2.beg_pos; */
                        arg_var(p, tid);
                        if (dyna_in_block(p)) {
                            YSTUB("grammar"); /* PORTME: $2->nd_value = NEW_DVAR(tid, &loc); */
                        }
                        else {
                            YSTUB("grammar"); /* PORTME: $2->nd_value = NEW_LVAR(tid, &loc); */
                        }
                        $$ = NEW_ARGS_AUX(tid, 1, &NULL_LOC);
                        YSTUB("grammar"); /* PORTME: $$->nd_next = (NODE *)$2; */
                    }
                ;

f_arg		: f_arg_item
                | f_arg ',' f_arg_item
                    {
                        $$ = $1;
                        if ($$ != NULL && $3 != NULL && PM_NODE_TYPE_P((NODE *) $$, PM_ARRAY_NODE) && PM_NODE_TYPE_P((NODE *) $3, PM_ARRAY_NODE)) {
                            pm_array_node_t *carrier = (pm_array_node_t *) $$;
                            pm_array_node_t *item = (pm_array_node_t *) $3;
                            for (size_t i = 0; i < item->elements.size; i++) {
                                pm_node_list_append(p->pm->arena, &carrier->elements, item->elements.nodes[i]);
                            }
                            uint32_t end = item->base.location.start + item->base.location.length;
                            carrier->base.location.length = end - carrier->base.location.start;
                        }
                        else {
                            YSTUB("f_arg append");
                        }
                        rb_discard_node(p, (NODE *)$3);
                    }
                ;


f_label 	: tLABEL
                    {
                        VALUE e = formal_argument_error(p, $$ = $1);
                        if (e) {
                            $$ = 0;
                        }
                        /*
                         * Workaround for Prism::ParseTest#test_filepath for
                         * "unparser/corpus/literal/def.txt"
                         *
                         * See the discussion on https://github.com/ruby/ruby/pull/9923
                         */
                        arg_var(p, ifdef_ripper(0, $1));
                        p->max_numparam = ORDINAL_PARAM;
                        p->ctxt.in_argdef = 0;
                    }
                ;

kwrest_mark	: tPOW
                | tDSTAR
                ;

f_no_kwarg	: p_kwnorest
                    {
                    }
                ;

f_kwrest	: kwrest_mark tIDENTIFIER
                    {
                        arg_var(p, shadowing_lvar(p, $2));
                        $$ = $2;
                        pm_ymarker_param(p, &p->ykwrest_param, 1, $2, &@1, &@2);
                    }
                | kwrest_mark
                    {
                        arg_var(p, idFWD_KWREST);
                        $$ = idFWD_KWREST;
                        pm_ymarker_param(p, &p->ykwrest_param, 1, 0, &@1, NULL);
                    }
                ;

restarg_mark	: '*'
                | tSTAR
                ;

f_rest_arg	: restarg_mark tIDENTIFIER
                    {
                        arg_var(p, shadowing_lvar(p, $2));
                        $$ = $2;
                        pm_ymarker_param(p, &p->yrest_param, 0, $2, &@1, &@2);
                    }
                | restarg_mark
                    {
                        arg_var(p, idFWD_REST);
                        $$ = idFWD_REST;
                        pm_ymarker_param(p, &p->yrest_param, 0, 0, &@1, NULL);
                    }
                ;

blkarg_mark	: '&'
                | tAMPER
                ;

f_block_arg	: blkarg_mark tIDENTIFIER
                    {
                        arg_var(p, shadowing_lvar(p, $2));
                        $$ = $2;
                        pm_ymarker_param(p, &p->yblock_param, 2, $2, &@1, &@2);
                    }
                | blkarg_mark keyword_nil
                    {
                        $$ = idNil;
                    }
                | blkarg_mark
                    {
                        arg_var(p, idFWD_BLOCK);
                        $$ = idFWD_BLOCK;
                        pm_ymarker_param(p, &p->yblock_param, 2, 0, &@1, NULL);
                    }
                ;

opt_comma	: ','?
                    {
                        $$ = 0;
                    }
                ;


singleton	: value_expr(singleton_expr)
                    {
                        NODE *expr = last_expr_node($1);
                        switch (nd_type(expr)) {
                          case NODE_STR:
                          case NODE_DSTR:
                          case NODE_XSTR:
                          case NODE_DXSTR:
                          case NODE_REGX:
                          case NODE_DREGX:
                          case NODE_SYM:
                          case NODE_LINE:
                          case NODE_FILE:
                          case NODE_ENCODING:
                          case NODE_INTEGER:
                          case NODE_FLOAT:
                          case NODE_RATIONAL:
                          case NODE_IMAGINARY:
                          case NODE_DSYM:
                          case NODE_LIST:
                          case NODE_ZLIST:
                            YSTUB("grammar"); /* PORTME: yyerror1(&expr->nd_loc, "can't define singleton method for literals"); */
                            break;
                          default:
                            break;
                        }
                        $$ = $1;
                    }
                ;

singleton_expr	: var_ref
                | '('
                    {
                        SET_LEX_STATE(EXPR_BEG);
                        p->ctxt.in_argdef = 0;
                    }
                  expr rparen
                    {
                        p->ctxt.in_argdef = 1;
                        $$ = $3;
                    }
                ;

assoc_list	: none
                | assocs trailer
                    {
                        $$ = $1;
                    }
                ;

assocs		: assoc
                | assocs ',' assoc
                    {
                        NODE *assocs = $1;
                        NODE *tail = $3;
                        if (!assocs) {
                            assocs = tail;
                        }
                        else if (tail) {
                            /* PORTME: CRuby merges a trailing bare ** hash
                             * into the previous element here. */
                            if (tail) {
                                assocs = list_concat(p, assocs, tail);
                            }
                        }
                        $$ = assocs;
                    }
                ;

assoc		: arg_value tASSOC arg_value
                    {
                        $$ = NEW_LIST(pm_yassoc(p, $1, $3, &@2, &@$), &@$);
                    }
                | tLABEL arg_value
                    {
                        $$ = NEW_LIST(pm_yassoc(p, pm_ylabel_symbol(p, $1, &@1), $2, NULL, &@$), &@$);
                    }
                | tLABEL
                    {
                        NODE *val = gettable(p, $1, &@$);
                        if (!val) val = NEW_ERROR(&@$);
                        $$ = NEW_LIST(pm_yassoc(p, pm_ylabel_symbol(p, $1, &@1), val, NULL, &@$), &@$);
                    }
                | tSTRING_BEG string_contents tLABEL_END arg_value
                    {
                        YYLTYPE loc = code_loc_gen(&@1, &@3);
                        $$ = list_append(p, NEW_LIST(dsym_node(p, $2, &loc), &loc), $4);
                    }
                | tDSTAR arg_value
                    {
                        $$ = NEW_LIST(pm_yassoc_splat(p, $2, &@1, &@$), &@$);
                    }
                | tDSTAR
                    {
                        forwarding_arg_check(p, idFWD_KWREST, idFWD_ALL, "keyword rest");
                        $$ = NEW_LIST(pm_yassoc_splat(p, NEW_LVAR(idFWD_KWREST, &@$), &@1, &@$), &@$);
                    }
                ;

%rule %inline operation : ident_or_const
                        | tFID
                        ;

operation2	: operation
                | op
                ;

operation3	: tIDENTIFIER
                | tFID
                | op
                ;

dot_or_colon	: '.'
                | tCOLON2
                ;

call_op 	: '.'
                | tANDDOT
                ;

call_op2	: call_op
                | tCOLON2
                ;

rparen		: '\n'? ')'
                ;

rbracket	: '\n'? ']'
                ;

rbrace		: '\n'? '}'
                ;

trailer		: '\n'?
                | ','
                ;

term		: ';'
                    {
                        yyerrok;
                        token_flush(p);
                        if (p->ctxt.in_defined) {
                            p->ctxt.has_trailing_semicolon = 1;
                        }
                    }
                | '\n'
                    {
                        @$.end = @$.beg;
                        token_flush(p);
                    }
                ;

terms		: term
                | terms ';' {yyerrok;}
                ;

none		: /* none */
                    {
                        $$ = 0;
                    }
                ;
%%
# undef p
# undef yylex
# undef yylval
# define yylval  (*p->lval)

static int regx_options(struct parser_params*);
static int tokadd_string(struct parser_params*,int,int,int,long*,rb_encoding**,rb_encoding**);
static void tokaddmbc(struct parser_params *p, int c, rb_encoding *enc);
static enum yytokentype parse_string(struct parser_params*,rb_strterm_literal_t*);
static enum yytokentype here_document(struct parser_params*,rb_strterm_heredoc_t*);

#define set_parser_s_value(x) (ifdef_ripper(p->s_value = (x), (void)0))

# define set_yylval_node(x) {				\
  YYLTYPE _cur_loc;					\
  rb_parser_set_location(p, &_cur_loc);			\
  yylval.node = (x);					\
  set_parser_s_value(STR_NEW(p->lex.ptok, p->lex.pcur-p->lex.ptok)); \
}
# define set_yylval_str(x) \
do { \
  set_yylval_node(NEW_STR(x, &_cur_loc)); \
  set_parser_s_value(rb_str_new_mutable_parser_string(x)); \
} while(0)
# define set_yylval_num(x) { \
  yylval.num = (x); \
  set_parser_s_value(x); \
}
# define set_yylval_id(x) (yylval.id = (x))
# define set_yylval_name(x) { \
  (yylval.id = (x)); \
  set_parser_s_value(ID2SYM(x)); \
}
# define yylval_id() (yylval.id)

#define set_yylval_noname() set_yylval_id(keyword_nil)
#define has_delayed_token(p) (p->delayed.token != NULL)

#define literal_flush(p, ptr) ((p)->lex.ptok = (ptr))
#define dispatch_scan_event(p, t) parser_dispatch_scan_event(p, t)
#define dispatch_delayed_token(p, t) ((void) 0)

/*
 * The half of CRuby's parser_dispatch_scan_event that is not about ripper or
 * kept tokens: publishing the token's location to the parser and flushing the
 * token start. Without this, every @N in the grammar is empty.
 */
static void
parser_dispatch_scan_event(struct parser_params *p, enum yytokentype t)
{
    (void) t;
    if (p->lex.pcur <= p->lex.ptok) return;

    RUBY_SET_YYLLOC(*p->yylloc);
    token_flush(p);
}
#define add_delayed_token(p, tok, end) ((void) 0)
#define dispatch_heredoc_end(p) ((void) 0)


static const char *
escaped_char(int c)
{
    switch (c) {
      case '"': return "\\\"";
      case '\\': return "\\\\";
      case '\0': return "\\0";
      case '\n': return "\\n";
      case '\r': return "\\r";
      case '\t': return "\\t";
      case '\f': return "\\f";
      case '\013': return "\\v";
      case '\010': return "\\b";
      case '\007': return "\\a";
      case '\033': return "\\e";
      case '\x7f': return "\\c?";
    }
    return NULL;
}





static inline int
is_identchar(struct parser_params *p, const char *ptr, const char *MAYBE_UNUSED(ptr_end), rb_encoding *enc)
{
    return rb_enc_isalnum((unsigned char)*ptr, enc) || *ptr == '_' || !ISASCII(*ptr);
}

static inline bool
peek_word_at(struct parser_params *p, const char *str, size_t len, int at)
{
    const char *ptr = p->lex.pcur + at;
    if (lex_eol_ptr_n_p(p, ptr, len-1)) return false;
    if (memcmp(ptr, str, len)) return false;
    if (lex_eol_ptr_n_p(p, ptr, len)) return true;
    switch (ptr[len]) {
      case '!': case '?': return false;
    }
    return !is_identchar(p, ptr+len, p->lex.pend, p->enc);
}

static inline int
parser_is_identchar(struct parser_params *p)
{
    return !(p)->eofp && is_identchar(p, p->lex.pcur-1, p->lex.pend, p->enc);
}

static inline int
parser_isascii(struct parser_params *p)
{
    return ISASCII(*(p->lex.pcur-1));
}

static void
token_info_setup(token_info *ptinfo, const char *ptr, const rb_code_location_t *loc)
{
    /* indentation warnings are not ported */
}

static void
token_info_push(struct parser_params *p, const char *token, const rb_code_location_t *loc)
{
    /* indentation warnings are not ported */
}

static void
token_info_pop(struct parser_params *p, const char *token, const rb_code_location_t *loc)
{
    /* indentation warnings are not ported */
}

static void
token_info_drop(struct parser_params *p, const char *token, rb_code_position_t beg_pos)
{
    /* indentation warnings are not ported */
}

static void
token_info_warn(struct parser_params *p, const char *token, token_info *ptinfo_beg, int same, const rb_code_location_t *loc)
{
    /* indentation warnings are not ported */
}

static int
parser_precise_mbclen(struct parser_params *p, const char *ptr)
{
    int len = rb_enc_precise_mbclen(ptr, p->lex.pend, p->enc);
    if (!MBCLEN_CHARFOUND_P(len)) {
        compile_error(p, "invalid multibyte char (%s)", rb_enc_name(p->enc));
        return -1;
    }
    return len;
}





static int
vtable_size(const struct vtable *tbl)
{
    if (!DVARS_TERMINAL_P(tbl)) {
        return tbl->pos;
    }
    else {
        return 0;
    }
}

static struct vtable *
vtable_alloc_gen(struct parser_params *p, int line, struct vtable *prev)
{
    struct vtable *tbl = ALLOC(struct vtable);
    tbl->pos = 0;
    tbl->capa = 8;
    tbl->tbl = ALLOC_N(ID, tbl->capa);
    tbl->prev = prev;
    if (p->debug) {
        rb_parser_printf(p, "vtable_alloc:%d: %p\n", line, (void *)tbl);
    }
    return tbl;
}
#define vtable_alloc(prev) vtable_alloc_gen(p, __LINE__, prev)

static void
vtable_free_gen(struct parser_params *p, int line, const char *name,
                struct vtable *tbl)
{
    if (p->debug) {
        rb_parser_printf(p, "vtable_free:%d: %s(%p)\n", line, name, (void *)tbl);
    }
    if (!DVARS_TERMINAL_P(tbl)) {
        if (tbl->tbl) {
            ruby_xfree_sized(tbl->tbl, tbl->capa * sizeof(ID));
        }
        ruby_xfree_sized(tbl, sizeof(*tbl));
    }
}
#define vtable_free(tbl) vtable_free_gen(p, __LINE__, #tbl, tbl)

static void
vtable_add_gen(struct parser_params *p, int line, const char *name,
               struct vtable *tbl, ID id)
{
    if (p->debug) {
        rb_parser_printf(p, "vtable_add:%d: %s(%p), %s\n",
                         line, name, (void *)tbl, rb_id2name(id));
    }
    if (DVARS_TERMINAL_P(tbl)) {
        rb_parser_fatal(p, "vtable_add: vtable is not allocated (%p)", (void *)tbl);
        return;
    }
    if (tbl->pos == tbl->capa) {
        tbl->capa = tbl->capa * 2;
        SIZED_REALLOC_N(tbl->tbl, ID, tbl->capa, tbl->pos);
    }
    tbl->tbl[tbl->pos++] = id;
}
#define vtable_add(tbl, id) vtable_add_gen(p, __LINE__, #tbl, tbl, id)

static void
vtable_pop_gen(struct parser_params *p, int line, const char *name,
               struct vtable *tbl, int n)
{
    if (p->debug) {
        rb_parser_printf(p, "vtable_pop:%d: %s(%p), %d\n",
                         line, name, (void *)tbl, n);
    }
    if (tbl->pos < n) {
        rb_parser_fatal(p, "vtable_pop: unreachable (%d < %d)", tbl->pos, n);
        return;
    }
    tbl->pos -= n;
}
#define vtable_pop(tbl, n) vtable_pop_gen(p, __LINE__, #tbl, tbl, n)

static int
vtable_included(const struct vtable * tbl, ID id)
{
    int i;

    if (!DVARS_TERMINAL_P(tbl)) {
        for (i = 0; i < tbl->pos; i++) {
            if (tbl->tbl[i] == id) {
                return i+1;
            }
        }
    }
    return 0;
}

static void parser_prepare(struct parser_params *p);

static int
e_option_supplied(struct parser_params *p)
{
    return (p->pm->command_line & PM_OPTIONS_COMMAND_LINE_E) != 0;
}

static NODE *parser_append_options(struct parser_params *p, NODE *node);



static rb_encoding *
must_be_ascii_compatible(struct parser_params *p, rb_parser_string_t *s)
{
    rb_encoding *enc = rb_parser_str_get_encoding(s);
    /* every encoding prism supports is ASCII compatible */
    return enc;
}

static rb_parser_string_t *
lex_getline(struct parser_params *p)
{
    const char *start = p->lex.gets_cursor;
    const char *end = (const char *) p->pm->end;

    if (start >= end) return 0;

    const char *nl = memchr(start, '\n', (size_t) (end - start));
    const char *stop = nl ? nl + 1 : end;
    p->lex.gets_cursor = stop;

    /* Record the next line's start offset, the same bookkeeping the
     * hand-written lexer does as it crosses each newline. The reader is the
     * one place every newline passes through exactly once, in order, even
     * while heredocs rewind the current line. */
    if (nl != NULL) pm_line_offset_list_append(&p->pm->metadata_arena, &p->pm->line_offsets, YOFF(stop));

    rb_parser_string_t *line = pm_ystring_new_shared(&p->pm->metadata_arena, start, (long) (stop - start), p->enc);
    p->line_count++;
    return line;
}


#define STR_FUNC_ESCAPE 0x01
#define STR_FUNC_EXPAND 0x02
#define STR_FUNC_REGEXP 0x04
#define STR_FUNC_QWORDS 0x08
#define STR_FUNC_SYMBOL 0x10
#define STR_FUNC_INDENT 0x20
#define STR_FUNC_LABEL  0x40
#define STR_FUNC_LIST   0x4000
#define STR_FUNC_TERM   0x8000

enum string_type {
    str_label  = STR_FUNC_LABEL,
    str_squote = (0),
    str_dquote = (STR_FUNC_EXPAND),
    str_xquote = (STR_FUNC_EXPAND),
    str_regexp = (STR_FUNC_REGEXP|STR_FUNC_ESCAPE|STR_FUNC_EXPAND),
    str_sword  = (STR_FUNC_QWORDS|STR_FUNC_LIST),
    str_dword  = (STR_FUNC_QWORDS|STR_FUNC_EXPAND|STR_FUNC_LIST),
    str_ssym   = (STR_FUNC_SYMBOL),
    str_dsym   = (STR_FUNC_SYMBOL|STR_FUNC_EXPAND)
};

static rb_parser_string_t *
parser_str_new(struct parser_params *p, const char *ptr, long len, rb_encoding *enc, int func, rb_encoding *enc0)
{
    rb_parser_string_t *pstr;

    pstr = rb_parser_encoding_string_new(p, ptr, len, enc);

    if (!(func & STR_FUNC_REGEXP)) {
        if (rb_parser_is_ascii_string(p, pstr)) {
        }
        else if (rb_is_usascii_enc((void *)enc0) && enc != rb_utf8_encoding()) {
            /* everything is valid in ASCII-8BIT */
            enc = rb_ascii8bit_encoding();
            PARSER_ENCODING_CODERANGE_SET(pstr, enc, RB_PARSER_ENC_CODERANGE_VALID);
        }
    }

    return pstr;
}

static int
strterm_is_heredoc(rb_strterm_t *strterm)
{
    return strterm->heredoc;
}

static rb_strterm_t *
new_strterm(struct parser_params *p, int func, int term, int paren)
{
    rb_strterm_t *strterm = ZALLOC(rb_strterm_t);
    strterm->u.literal.func = func;
    strterm->u.literal.term = term;
    strterm->u.literal.paren = paren;
    return strterm;
}

static rb_strterm_t *
new_heredoc(struct parser_params *p)
{
    rb_strterm_t *strterm = ZALLOC(rb_strterm_t);
    strterm->heredoc = true;
    return strterm;
}

#define peek(p,c) peek_n(p, (c), 0)
#define peek_n(p,c,n) (!lex_eol_n_p(p, n) && (c) == (unsigned char)(p)->lex.pcur[n])
#define peekc(p) peekc_n(p, 0)
#define peekc_n(p,n) (lex_eol_n_p(p, n) ? -1 : (unsigned char)(p)->lex.pcur[n])


static void
set_lastline(struct parser_params *p, rb_parser_string_t *str)
{
    p->lex.pbeg = p->lex.pcur = PARSER_STRING_PTR(str);
    p->lex.pend = p->lex.pcur + PARSER_STRING_LEN(str);
    p->lex.lastline = str;
}

static int
nextline(struct parser_params *p, int set_encoding)
{
    rb_parser_string_t *str = p->lex.nextline;
    p->lex.nextline = 0;
    if (!str) {
        if (p->eofp)
            return -1;

        if (!lex_eol_ptr_p(p, p->lex.pbeg) && *(p->lex.pend-1) != '\n') {
            goto end_of_input;
        }

        if (!(str = lex_getline(p))) {
          end_of_input:
            p->eofp = 1;
            lex_goto_eol(p);
            return -1;
        }
        p->cr_seen = FALSE;
    }
    else if (str == AFTER_HEREDOC_WITHOUT_TERMINATOR) {
        /* after here-document without terminator */
        goto end_of_input;
    }
    add_delayed_token(p, p->lex.ptok, p->lex.pend);
    if (p->heredoc_end > 0) {
        p->ruby_sourceline = p->heredoc_end;
        p->heredoc_end = 0;
    }
    p->ruby_sourceline++;
    set_lastline(p, str);
    token_flush(p);
    return 0;
}

static int
parser_cr(struct parser_params *p, int c)
{
    if (peek(p, '\n')) {
        p->lex.pcur++;
        c = '\n';
    }
    return c;
}

static inline int
nextc0(struct parser_params *p, int set_encoding)
{
    int c;

    if (UNLIKELY(lex_eol_p(p) || p->eofp || p->lex.nextline > AFTER_HEREDOC_WITHOUT_TERMINATOR)) {
        if (nextline(p, set_encoding)) return -1;
    }
    c = (unsigned char)*p->lex.pcur++;
    if (UNLIKELY(c == '\r')) {
        c = parser_cr(p, c);
    }

    return c;
}
#define nextc(p) nextc0(p, TRUE)

static void
pushback(struct parser_params *p, int c)
{
    if (c == -1) return;
    p->eofp = 0;
    p->lex.pcur--;
    if (p->lex.pcur > p->lex.pbeg && p->lex.pcur[0] == '\n' && p->lex.pcur[-1] == '\r') {
        p->lex.pcur--;
    }
}

#define was_bol(p) ((p)->lex.pcur == (p)->lex.pbeg + 1)

#define tokfix(p) ((p)->tokenbuf[(p)->tokidx]='\0')
#define tok(p) (p)->tokenbuf
#define toklen(p) (p)->tokidx

static int
looking_at_eol_p(struct parser_params *p)
{
    const char *ptr = p->lex.pcur;
    while (!lex_eol_ptr_p(p, ptr)) {
        int c = (unsigned char)*ptr++;
        int eol = (c == '\n' || c == '#');
        if (eol || !ISSPACE(c)) {
            return eol;
        }
    }
    return TRUE;
}

static char*
newtok(struct parser_params *p)
{
    p->tokidx = 0;
    if (!p->tokenbuf) {
        p->toksiz = 60;
        p->tokenbuf = ALLOC_N(char, 60);
    }
    if (p->toksiz > 4096) {
        p->toksiz = 60;
        REALLOC_N(p->tokenbuf, char, 60);
    }
    return p->tokenbuf;
}

static char *
tokspace(struct parser_params *p, int n)
{
    p->tokidx += n;

    if (p->tokidx >= p->toksiz) {
        do {p->toksiz *= 2;} while (p->toksiz < p->tokidx);
        REALLOC_N(p->tokenbuf, char, p->toksiz);
    }
    return &p->tokenbuf[p->tokidx-n];
}

static void
tokadd(struct parser_params *p, int c)
{
    p->tokenbuf[p->tokidx++] = (char)c;
    if (p->tokidx >= p->toksiz) {
        p->toksiz *= 2;
        REALLOC_N(p->tokenbuf, char, p->toksiz);
    }
}

static int
tok_hex(struct parser_params *p, size_t *numlen)
{
    int c;

    c = (int)ruby_scan_hex(p->lex.pcur, 2, numlen);
    if (!*numlen) {
        flush_string_content(p, p->enc, rb_strlen_lit("\\x"));
        yyerror0("invalid hex escape");
        dispatch_scan_event(p, tSTRING_CONTENT);
        return 0;
    }
    p->lex.pcur += *numlen;
    return c;
}

#define tokcopy(p, n) memcpy(tokspace(p, n), (p)->lex.pcur - (n), (n))

static int
escaped_control_code(int c)
{
    int c2 = 0;
    switch (c) {
      case ' ':
        c2 = 's';
        break;
      case '\n':
        c2 = 'n';
        break;
      case '\t':
        c2 = 't';
        break;
      case '\v':
        c2 = 'v';
        break;
      case '\r':
        c2 = 'r';
        break;
      case '\f':
        c2 = 'f';
        break;
    }
    return c2;
}

#define WARN_SPACE_CHAR(c, prefix) \
    rb_warn1("invalid character syntax; use "prefix"\\%c", WARN_I(c))

static int
tokadd_codepoint(struct parser_params *p, rb_encoding **encp,
                 int regexp_literal, const char *begin)
{
    const int wide = !begin;
    size_t numlen;
    int codepoint = (int)ruby_scan_hex(p->lex.pcur, wide ? p->lex.pend - p->lex.pcur : 4, &numlen);

    p->lex.pcur += numlen;
    if (p->lex.strterm == NULL ||
        strterm_is_heredoc(p->lex.strterm) ||
        (p->lex.strterm->u.literal.func != str_regexp)) {
        if (!begin) begin = p->lex.pcur;
        if (wide ? (numlen == 0 || numlen > 6) : (numlen < 4))  {
            flush_string_content(p, rb_utf8_encoding(), p->lex.pcur - begin);
            yyerror0("invalid Unicode escape");
            dispatch_scan_event(p, tSTRING_CONTENT);
            return wide && numlen > 0;
        }
        if (codepoint > 0x10ffff) {
            flush_string_content(p, rb_utf8_encoding(), p->lex.pcur - begin);
            yyerror0("invalid Unicode codepoint (too large)");
            dispatch_scan_event(p, tSTRING_CONTENT);
            return wide;
        }
        if ((codepoint & 0xfffff800) == 0xd800) {
            flush_string_content(p, rb_utf8_encoding(), p->lex.pcur - begin);
            yyerror0("invalid Unicode codepoint");
            dispatch_scan_event(p, tSTRING_CONTENT);
            return wide;
        }
    }
    if (regexp_literal) {
        tokcopy(p, (int)numlen);
    }
    else if (codepoint >= 0x80) {
        rb_encoding *utf8 = rb_utf8_encoding();
        if (*encp && utf8 != *encp) {
            YYLTYPE loc = RUBY_INIT_YYLLOC();
            compile_error(p, "UTF-8 mixed within %s source", rb_enc_name(*encp));
            parser_show_error_line(p, &loc);
            return wide;
        }
        *encp = utf8;
        tokaddmbc(p, codepoint, *encp);
    }
    else {
        tokadd(p, codepoint);
    }
    return TRUE;
}

static int tokadd_mbchar(struct parser_params *p, int c);

static int
tokskip_mbchar(struct parser_params *p)
{
    int len = parser_precise_mbclen(p, p->lex.pcur-1);
    if (len > 0) {
        p->lex.pcur += len - 1;
    }
    return len;
}

/* return value is for ?\u3042 */
static void
tokadd_utf8(struct parser_params *p, rb_encoding **encp,
            int term, int symbol_literal, int regexp_literal)
{
    /*
     * If `term` is not -1, then we allow multiple codepoints in \u{}
     * upto `term` byte, otherwise we're parsing a character literal.
     * And then add the codepoints to the current token.
     */
    static const char multiple_codepoints[] = "Multiple codepoints at single character literal";

    const int open_brace = '{', close_brace = '}';

    if (regexp_literal) { tokadd(p, '\\'); tokadd(p, 'u'); }

    if (peek(p, open_brace)) {  /* handle \u{...} form */
        if (regexp_literal && p->lex.strterm->u.literal.func == str_regexp) {
            /*
             * Skip parsing validation code and copy bytes as-is until term or
             * closing brace, in order to correctly handle extended regexps where
             * invalid unicode escapes are allowed in comments. The regexp parser
             * does its own validation and will catch any issues.
             */
            tokadd(p, open_brace);
            while (!lex_eol_ptr_p(p, ++p->lex.pcur)) {
                int c = peekc(p);
                if (c == close_brace) {
                    tokadd(p, c);
                    ++p->lex.pcur;
                    break;
                }
                else if (c == term) {
                    break;
                }
                if (c == '\\' && !lex_eol_n_p(p, 1)) {
                    tokadd(p, c);
                    c = *++p->lex.pcur;
                }
                tokadd_mbchar(p, c);
            }
        }
        else {
            const char *second = NULL;
            int c, last = nextc(p);
            if (lex_eol_p(p)) goto unterminated;
            while (ISSPACE(c = peekc(p)) && !lex_eol_ptr_p(p, ++p->lex.pcur));
            while (c != close_brace) {
                if (c == term) goto unterminated;
                if (second == multiple_codepoints)
                    second = p->lex.pcur;
                if (regexp_literal) tokadd(p, last);
                if (!tokadd_codepoint(p, encp, regexp_literal, NULL)) {
                    break;
                }
                while (ISSPACE(c = peekc(p))) {
                    if (lex_eol_ptr_p(p, ++p->lex.pcur)) goto unterminated;
                    last = c;
                }
                if (term == -1 && !second)
                    second = multiple_codepoints;
            }

            if (c != close_brace) {
              unterminated:
                flush_string_content(p, rb_utf8_encoding(), 0);
                yyerror0("unterminated Unicode escape");
                dispatch_scan_event(p, tSTRING_CONTENT);
                return;
            }
            if (second && second != multiple_codepoints) {
                const char *pcur = p->lex.pcur;
                p->lex.pcur = second;
                dispatch_scan_event(p, tSTRING_CONTENT);
                token_flush(p);
                p->lex.pcur = pcur;
                yyerror0(multiple_codepoints);
                token_flush(p);
            }

            if (regexp_literal) tokadd(p, close_brace);
            nextc(p);
        }
    }
    else {			/* handle \uxxxx form */
        if (!tokadd_codepoint(p, encp, regexp_literal, p->lex.pcur - rb_strlen_lit("\\u"))) {
            token_flush(p);
            return;
        }
    }
}

#define ESCAPE_CONTROL 1
#define ESCAPE_META    2

static int
read_escape(struct parser_params *p, int flags, const char *begin)
{
    int c;
    size_t numlen;

    switch (c = nextc(p)) {
      case '\\':	/* Backslash */
        return c;

      case 'n':	/* newline */
        return '\n';

      case 't':	/* horizontal tab */
        return '\t';

      case 'r':	/* carriage-return */
        return '\r';

      case 'f':	/* form-feed */
        return '\f';

      case 'v':	/* vertical tab */
        return '\13';

      case 'a':	/* alarm(bell) */
        return '\007';

      case 'e':	/* escape */
        return 033;

      case '0': case '1': case '2': case '3': /* octal constant */
      case '4': case '5': case '6': case '7':
        pushback(p, c);
        c = (int)ruby_scan_oct(p->lex.pcur, 3, &numlen);
        p->lex.pcur += numlen;
        return c;

      case 'x':	/* hex constant */
        c = tok_hex(p, &numlen);
        if (numlen == 0) return 0;
        return c;

      case 'b':	/* backspace */
        return '\010';

      case 's':	/* space */
        return ' ';

      case 'M':
        if (flags & ESCAPE_META) goto eof;
        if ((c = nextc(p)) != '-') {
            goto eof;
        }
        if ((c = nextc(p)) == '\\') {
            switch (peekc(p)) {
              case 'u': case 'U':
                nextc(p);
                goto eof;
            }
            return read_escape(p, flags|ESCAPE_META, begin) | 0x80;
        }
        else if (c == -1) goto eof;
        else if (!ISASCII(c)) {
            tokskip_mbchar(p);
            goto eof;
        }
        else {
            int c2 = escaped_control_code(c);
            if (c2) {
                if (ISCNTRL(c) || !(flags & ESCAPE_CONTROL)) {
                    WARN_SPACE_CHAR(c2, "\\M-");
                }
                else {
                    WARN_SPACE_CHAR(c2, "\\C-\\M-");
                }
            }
            else if (ISCNTRL(c)) goto eof;
            return ((c & 0xff) | 0x80);
        }

      case 'C':
        if ((c = nextc(p)) != '-') {
            goto eof;
        }
      case 'c':
        if (flags & ESCAPE_CONTROL) goto eof;
        if ((c = nextc(p))== '\\') {
            switch (peekc(p)) {
              case 'u': case 'U':
                nextc(p);
                goto eof;
            }
            c = read_escape(p, flags|ESCAPE_CONTROL, begin);
        }
        else if (c == '?')
            return 0177;
        else if (c == -1) goto eof;
        else if (!ISASCII(c)) {
            tokskip_mbchar(p);
            goto eof;
        }
        else {
            int c2 = escaped_control_code(c);
            if (c2) {
                if (ISCNTRL(c)) {
                    if (flags & ESCAPE_META) {
                        WARN_SPACE_CHAR(c2, "\\M-");
                    }
                    else {
                        WARN_SPACE_CHAR(c2, "");
                    }
                }
                else {
                    if (flags & ESCAPE_META) {
                        WARN_SPACE_CHAR(c2, "\\M-\\C-");
                    }
                    else {
                        WARN_SPACE_CHAR(c2, "\\C-");
                    }
                }
            }
            else if (ISCNTRL(c)) goto eof;
        }
        return c & 0x9f;

      eof:
      case -1:
        flush_string_content(p, p->enc, p->lex.pcur - begin);
        yyerror0("Invalid escape character syntax");
        dispatch_scan_event(p, tSTRING_CONTENT);
        return '\0';

      default:
        if (!ISASCII(c)) {
            tokskip_mbchar(p);
            goto eof;
        }
        return c;
    }
}

static void
tokaddmbc(struct parser_params *p, int c, rb_encoding *enc)
{
    int len = rb_enc_codelen(c, enc);
    rb_enc_mbcput(c, tokspace(p, len), enc);
}

static int
tokadd_escape(struct parser_params *p)
{
    int c;
    size_t numlen;
    const char *begin = p->lex.pcur;

    switch (c = nextc(p)) {
      case '\n':
        return 0;		/* just ignore */

      case '0': case '1': case '2': case '3': /* octal constant */
      case '4': case '5': case '6': case '7':
        {
            ruby_scan_oct(--p->lex.pcur, 3, &numlen);
            if (numlen == 0) goto eof;
            p->lex.pcur += numlen;
            tokcopy(p, (int)numlen + 1);
        }
        return 0;

      case 'x':	/* hex constant */
        {
            tok_hex(p, &numlen);
            if (numlen == 0) return -1;
            tokcopy(p, (int)numlen + 2);
        }
        return 0;

      eof:
      case -1:
        flush_string_content(p, p->enc, p->lex.pcur - begin);
        yyerror0("Invalid escape character syntax");
        token_flush(p);
        return -1;

      default:
        tokadd(p, '\\');
        tokadd(p, c);
    }
    return 0;
}

static int
char_to_option(int c)
{
    int val;

    switch (c) {
      case 'i':
        val = RE_ONIG_OPTION_IGNORECASE;
        break;
      case 'x':
        val = RE_ONIG_OPTION_EXTEND;
        break;
      case 'm':
        val = RE_ONIG_OPTION_MULTILINE;
        break;
      default:
        val = 0;
        break;
    }
    return val;
}

#define ARG_ENCODING_FIXED   16
#define ARG_ENCODING_NONE    32
#define ENC_ASCII8BIT   1
#define ENC_EUC_JP      2
#define ENC_Windows_31J 3
#define ENC_UTF8        4

static int
char_to_option_kcode(int c, int *option, int *kcode)
{
    *option = 0;

    switch (c) {
      case 'n':
        *kcode = ENC_ASCII8BIT;
        return (*option = ARG_ENCODING_NONE);
      case 'e':
        *kcode = ENC_EUC_JP;
        break;
      case 's':
        *kcode = ENC_Windows_31J;
        break;
      case 'u':
        *kcode = ENC_UTF8;
        break;
      default:
        *kcode = -1;
        return (*option = char_to_option(c));
    }
    *option = ARG_ENCODING_FIXED;
    return 1;
}

static int
regx_options(struct parser_params *p)
{
    int kcode = 0;
    int kopt = 0;
    int options = 0;
    int c, opt, kc;

    newtok(p);
    while (c = nextc(p), ISALPHA(c)) {
        if (c == 'o') {
            options |= RE_OPTION_ONCE;
        }
        else if (char_to_option_kcode(c, &opt, &kc)) {
            if (kc >= 0) {
                if (kc != ENC_ASCII8BIT) kcode = c;
                kopt = opt;
            }
            else {
                options |= opt;
            }
        }
        else {
            tokadd(p, c);
        }
    }
    options |= kopt;
    pushback(p, c);
    if (toklen(p)) {
        YYLTYPE loc = RUBY_INIT_YYLLOC();
        tokfix(p);
        compile_error(p, "unknown regexp option%s - %*s",
                      toklen(p) > 1 ? "s" : "", toklen(p), tok(p));
        parser_show_error_line(p, &loc);
    }
    return options | RE_OPTION_ENCODING(kcode);
}

static int
tokadd_mbchar(struct parser_params *p, int c)
{
    int len = parser_precise_mbclen(p, p->lex.pcur-1);
    if (len < 0) return -1;
    tokadd(p, c);
    p->lex.pcur += --len;
    if (len > 0) tokcopy(p, len);
    return c;
}

static inline int
simple_re_meta(int c)
{
    switch (c) {
      case '$': case '*': case '+': case '.':
      case '?': case '^': case '|':
      case ')': case ']': case '}': case '>':
        return TRUE;
      default:
        return FALSE;
    }
}

static int
parser_update_heredoc_indent(struct parser_params *p, int c)
{
    if (p->heredoc_line_indent == -1) {
        if (c == '\n') p->heredoc_line_indent = 0;
    }
    else {
        if (c == ' ') {
            p->heredoc_line_indent++;
            return TRUE;
        }
        else if (c == '\t') {
            int w = (p->heredoc_line_indent / TAB_WIDTH) + 1;
            p->heredoc_line_indent = w * TAB_WIDTH;
            return TRUE;
        }
        else if (c != '\n') {
            if (p->heredoc_indent > p->heredoc_line_indent) {
                p->heredoc_indent = p->heredoc_line_indent;
            }
            p->heredoc_line_indent = -1;
        }
        else {
            /* Whitespace only line has no indentation */
            p->heredoc_line_indent = 0;
        }
    }
    return FALSE;
}

static void
parser_mixed_error(struct parser_params *p, rb_encoding *enc1, rb_encoding *enc2)
{
    YYLTYPE loc = RUBY_INIT_YYLLOC();
    const char *n1 = rb_enc_name(enc1), *n2 = rb_enc_name(enc2);
    compile_error(p, "%s mixed within %s source", n1, n2);
    parser_show_error_line(p, &loc);
}

static void
parser_mixed_escape(struct parser_params *p, const char *beg, rb_encoding *enc1, rb_encoding *enc2)
{
    const char *pos = p->lex.pcur;
    p->lex.pcur = beg;
    parser_mixed_error(p, enc1, enc2);
    p->lex.pcur = pos;
}

static inline char
nibble_char_upper(unsigned int c)
{
    c &= 0xf;
    return c + (c < 10 ? '0' : 'A' - 10);
}

static int
tokadd_string(struct parser_params *p,
              int func, int term, int paren, long *nest,
              rb_encoding **encp, rb_encoding **enc)
{
    int c;
    bool erred = false;

#define mixed_error(enc1, enc2) \
    (void)(erred || (parser_mixed_error(p, enc1, enc2), erred = true))
#define mixed_escape(beg, enc1, enc2) \
    (void)(erred || (parser_mixed_escape(p, beg, enc1, enc2), erred = true))

    while ((c = nextc(p)) != -1) {
        if (p->heredoc_indent > 0) {
            parser_update_heredoc_indent(p, c);
        }

        if (paren && c == paren) {
            ++*nest;
        }
        else if (c == term) {
            if (!nest || !*nest) {
                pushback(p, c);
                break;
            }
            --*nest;
        }
        else if ((func & STR_FUNC_EXPAND) && c == '#' && !lex_eol_p(p)) {
            unsigned char c2 = *p->lex.pcur;
            if (c2 == '$' || c2 == '@' || c2 == '{') {
                pushback(p, c);
                break;
            }
        }
        else if (c == '\\') {
            c = nextc(p);
            switch (c) {
              case '\n':
                if (func & STR_FUNC_QWORDS) break;
                if (func & STR_FUNC_EXPAND) {
                    if (!(func & STR_FUNC_INDENT) || (p->heredoc_indent < 0))
                        continue;
                    if (c == term) {
                        c = '\\';
                        goto terminate;
                    }
                }
                tokadd(p, '\\');
                break;

              case '\\':
                if (func & STR_FUNC_ESCAPE) tokadd(p, c);
                break;

              case 'u':
                if ((func & STR_FUNC_EXPAND) == 0) {
                    tokadd(p, '\\');
                    break;
                }
                tokadd_utf8(p, enc, term,
                            func & STR_FUNC_SYMBOL,
                            func & STR_FUNC_REGEXP);
                continue;

              default:
                if (c == -1) return -1;
                if (!ISASCII(c)) {
                    if ((func & STR_FUNC_EXPAND) == 0) tokadd(p, '\\');
                    goto non_ascii;
                }
                if (func & STR_FUNC_REGEXP) {
                    switch (c) {
                      case 'c':
                      case 'C':
                      case 'M': {
                        pushback(p, c);
                        c = read_escape(p, 0, p->lex.pcur - 1);

                        char *t = tokspace(p, rb_strlen_lit("\\x00"));
                        *t++ = '\\';
                        *t++ = 'x';
                        *t++ = nibble_char_upper(c >> 4);
                        *t++ = nibble_char_upper(c);
                        continue;
                      }
                    }

                    if (c == term && !simple_re_meta(c)) {
                        tokadd(p, c);
                        continue;
                    }
                    pushback(p, c);
                    if ((c = tokadd_escape(p)) < 0)
                        return -1;
                    if (*enc && *enc != *encp) {
                        mixed_escape(p->lex.ptok+2, *enc, *encp);
                    }
                    continue;
                }
                else if (func & STR_FUNC_EXPAND) {
                    pushback(p, c);
                    if (func & STR_FUNC_ESCAPE) tokadd(p, '\\');
                    c = read_escape(p, 0, p->lex.pcur - 1);
                }
                else if ((func & STR_FUNC_QWORDS) && ISSPACE(c)) {
                    /* ignore backslashed spaces in %w */
                }
                else if (c != term && !(paren && c == paren)) {
                    tokadd(p, '\\');
                    pushback(p, c);
                    continue;
                }
            }
        }
        else if (!parser_isascii(p)) {
          non_ascii:
            if (!*enc) {
                *enc = *encp;
            }
            else if (*enc != *encp) {
                mixed_error(*enc, *encp);
                continue;
            }
            if (tokadd_mbchar(p, c) == -1) return -1;
            continue;
        }
        else if ((func & STR_FUNC_QWORDS) && ISSPACE(c)) {
            pushback(p, c);
            break;
        }
        if (c & 0x80) {
            if (!*enc) {
                *enc = *encp;
            }
            else if (*enc != *encp) {
                mixed_error(*enc, *encp);
                continue;
            }
        }
        tokadd(p, c);
    }
  terminate:
    if (*enc) *encp = *enc;
    return c;
}

#define NEW_STRTERM(func, term, paren) new_strterm(p, func, term, paren)

static void
flush_string_content(struct parser_params *p, rb_encoding *enc, size_t back)
{
    p->lex.pcur -= back;
    if (has_delayed_token(p)) {
        ptrdiff_t len = p->lex.pcur - p->lex.ptok;
        if (len > 0) {
            rb_parser_enc_str_buf_cat(p, p->delayed.token, p->lex.ptok, len, enc);
            p->delayed.end_line = p->ruby_sourceline;
            p->delayed.end_col = rb_long2int(p->lex.pcur - p->lex.pbeg);
        }
        dispatch_delayed_token(p, tSTRING_CONTENT);
        p->lex.ptok = p->lex.pcur;
    }
    dispatch_scan_event(p, tSTRING_CONTENT);
    p->lex.pcur += back;
}

/* this can be shared with ripper, since it's independent from struct
 * parser_params. */
#define BIT(c, idx) (((c) / 32 - 1 == idx) ? (1U << ((c) % 32)) : 0)
#define SPECIAL_PUNCT(idx) ( \
        BIT('~', idx) | BIT('*', idx) | BIT('$', idx) | BIT('?', idx) | \
        BIT('!', idx) | BIT('@', idx) | BIT('/', idx) | BIT('\\', idx) | \
        BIT(';', idx) | BIT(',', idx) | BIT('.', idx) | BIT('=', idx) | \
        BIT(':', idx) | BIT('<', idx) | BIT('>', idx) | BIT('\"', idx) | \
        BIT('&', idx) | BIT('`', idx) | BIT('\'', idx) | BIT('+', idx) | \
        BIT('0', idx))
static const uint_least32_t ruby_global_name_punct_bits[] = {
    SPECIAL_PUNCT(0),
    SPECIAL_PUNCT(1),
    SPECIAL_PUNCT(2),
};
#undef BIT
#undef SPECIAL_PUNCT

static enum yytokentype
parser_peek_variable_name(struct parser_params *p)
{
    int c;
    const char *ptr = p->lex.pcur;

    if (lex_eol_ptr_n_p(p, ptr, 1)) return 0;
    c = *ptr++;
    switch (c) {
      case '$':
        if ((c = *ptr) == '-') {
            if (lex_eol_ptr_p(p, ++ptr)) return 0;
            c = *ptr;
        }
        else if (is_global_name_punct(c) || ISDIGIT(c)) {
            return tSTRING_DVAR;
        }
        break;
      case '@':
        if ((c = *ptr) == '@') {
            if (lex_eol_ptr_p(p, ++ptr)) return 0;
            c = *ptr;
        }
        break;
      case '{':
        p->lex.pcur = ptr;
        p->command_start = TRUE;
        yylval.state = p->lex.state;
        return tSTRING_DBEG;
      default:
        return 0;
    }
    if (!ISASCII(c) || c == '_' || ISALPHA(c))
        return tSTRING_DVAR;
    return 0;
}

#define IS_ARG() IS_lex_state(EXPR_ARG_ANY)
#define IS_END() IS_lex_state(EXPR_END_ANY)
#define IS_BEG() (IS_lex_state(EXPR_BEG_ANY) || IS_lex_state_all(EXPR_ARG|EXPR_LABELED))
#define IS_SPCARG(c) (IS_ARG() && space_seen && !ISSPACE(c))
#define IS_LABEL_POSSIBLE() (\
        (IS_lex_state(EXPR_LABEL|EXPR_ENDFN) && !cmd_state) || \
        IS_ARG())
#define IS_LABEL_SUFFIX(n) (peek_n(p, ':',(n)) && !peek_n(p, ':', (n)+1))
#define IS_AFTER_OPERATOR() IS_lex_state(EXPR_FNAME | EXPR_DOT)

static inline enum yytokentype
parser_string_term(struct parser_params *p, int func)
{
    xfree(p->lex.strterm);
    p->lex.strterm = 0;
    if (func & STR_FUNC_REGEXP) {
        set_yylval_num(regx_options(p));
        dispatch_scan_event(p, tREGEXP_END);
        SET_LEX_STATE(EXPR_END);
        return tREGEXP_END;
    }
    if ((func & STR_FUNC_LABEL) && IS_LABEL_SUFFIX(0)) {
        nextc(p);
        SET_LEX_STATE(EXPR_ARG|EXPR_LABELED);
        return tLABEL_END;
    }
    SET_LEX_STATE(EXPR_END);
    return tSTRING_END;
}

static enum yytokentype
parse_string(struct parser_params *p, rb_strterm_literal_t *quote)
{
    int func = quote->func;
    int term = quote->term;
    int paren = quote->paren;
    int c, space = 0;
    rb_encoding *enc = p->enc;
    rb_encoding *base_enc = 0;
    rb_parser_string_t *lit;

    if (func & STR_FUNC_TERM) {
        if (func & STR_FUNC_QWORDS) nextc(p); /* delayed term */
        SET_LEX_STATE(EXPR_END);
        xfree(p->lex.strterm);
        p->lex.strterm = 0;
        return func & STR_FUNC_REGEXP ? tREGEXP_END : tSTRING_END;
    }
    c = nextc(p);
    if ((func & STR_FUNC_QWORDS) && ISSPACE(c)) {
        while (c != '\n' && ISSPACE(c = nextc(p)));
        space = 1;
    }
    if (func & STR_FUNC_LIST) {
        quote->func &= ~STR_FUNC_LIST;
        space = 1;
    }
    if (c == term && !quote->nest) {
        if (func & STR_FUNC_QWORDS) {
            quote->func |= STR_FUNC_TERM;
            pushback(p, c); /* dispatch the term at tSTRING_END */
            add_delayed_token(p, p->lex.ptok, p->lex.pcur);
            return ' ';
        }
        return parser_string_term(p, func);
    }
    if (space) {
        if (!ISSPACE(c)) pushback(p, c);
        add_delayed_token(p, p->lex.ptok, p->lex.pcur);
        return ' ';
    }
    newtok(p);
    if ((func & STR_FUNC_EXPAND) && c == '#') {
        enum yytokentype t = parser_peek_variable_name(p);
        if (t) return t;
        tokadd(p, '#');
        c = nextc(p);
    }
    pushback(p, c);
    if (tokadd_string(p, func, term, paren, &quote->nest,
                      &enc, &base_enc) == -1) {
        if (p->eofp) {
# define unterminated_literal(mesg) yyerror0(mesg)
            literal_flush(p, p->lex.pcur);
            if (func & STR_FUNC_QWORDS) {
                /* no content to add, bailing out here */
                unterminated_literal("unterminated list meets end of file");
                xfree(p->lex.strterm);
                p->lex.strterm = 0;
                return tSTRING_END;
            }
            if (func & STR_FUNC_REGEXP) {
                unterminated_literal("unterminated regexp meets end of file");
            }
            else {
                unterminated_literal("unterminated string meets end of file");
            }
            quote->func |= STR_FUNC_TERM;
        }
    }

    tokfix(p);
    lit = STR_NEW3(tok(p), toklen(p), enc, func);
    set_yylval_str(lit);
    flush_string_content(p, enc, 0);

    return tSTRING_CONTENT;
}

static enum yytokentype
heredoc_identifier(struct parser_params *p)
{
    /*
     * term_len is length of `<<"END"` except `END`,
     * in this case term_len is 4 (<, <, " and ").
     */
    long len, offset = p->lex.pcur - p->lex.pbeg;
    int c = nextc(p), term, func = 0, quote = 0;
    enum yytokentype token = tSTRING_BEG;
    int indent = 0;

    if (c == '-') {
        c = nextc(p);
        func = STR_FUNC_INDENT;
        offset++;
    }
    else if (c == '~') {
        c = nextc(p);
        func = STR_FUNC_INDENT;
        offset++;
        indent = INT_MAX;
    }
    switch (c) {
      case '\'':
        func |= str_squote; goto quoted;
      case '"':
        func |= str_dquote; goto quoted;
      case '`':
        token = tXSTRING_BEG;
        func |= str_xquote; goto quoted;

      quoted:
        quote++;
        offset++;
        term = c;
        len = 0;
        while ((c = nextc(p)) != term) {
            if (c == -1 || c == '\r' || c == '\n') {
                yyerror0("unterminated here document identifier");
                return -1;
            }
        }
        break;

      default:
        if (!parser_is_identchar(p)) {
            pushback(p, c);
            if (func & STR_FUNC_INDENT) {
                pushback(p, indent > 0 ? '~' : '-');
            }
            return 0;
        }
        func |= str_dquote;
        do {
            int n = parser_precise_mbclen(p, p->lex.pcur-1);
            if (n < 0) return 0;
            p->lex.pcur += --n;
        } while ((c = nextc(p)) != -1 && parser_is_identchar(p));
        pushback(p, c);
        break;
    }

    len = p->lex.pcur - (p->lex.pbeg + offset) - quote;
    if ((unsigned long)len >= HERETERM_LENGTH_MAX)
        yyerror0("too long here document identifier");
    dispatch_scan_event(p, tHEREDOC_BEG);
    lex_goto_eol(p);

    p->lex.strterm = new_heredoc(p);
    rb_strterm_heredoc_t *here = &p->lex.strterm->u.heredoc;
    here->offset = offset;
    here->sourceline = p->ruby_sourceline;
    here->length = (unsigned)len;
    here->quote = quote;
    here->func = func;
    here->lastline = p->lex.lastline;

    token_flush(p);
    p->heredoc_indent = indent;
    p->heredoc_line_indent = 0;
    return token;
}

static void
heredoc_restore(struct parser_params *p, rb_strterm_heredoc_t *here)
{
    rb_parser_string_t *line;
    rb_strterm_t *term = p->lex.strterm;

    p->lex.strterm = 0;
    line = here->lastline;
    p->lex.lastline = line;
    p->lex.pbeg = PARSER_STRING_PTR(line);
    p->lex.pend = p->lex.pbeg + PARSER_STRING_LEN(line);
    p->lex.pcur = p->lex.pbeg + here->offset + here->length + here->quote;
    p->lex.ptok = p->lex.pbeg + here->offset - here->quote;
    p->heredoc_end = p->ruby_sourceline;
    p->ruby_sourceline = (int)here->sourceline;
    if (p->eofp) p->lex.nextline = AFTER_HEREDOC_WITHOUT_TERMINATOR;
    p->eofp = 0;
    xfree(term);
}

static int
dedent_string_column(const char *str, long len, int width)
{
    int i, col = 0;

    for (i = 0; i < len && col < width; i++) {
        if (str[i] == ' ') {
            col++;
        }
        else if (str[i] == '\t') {
            int n = TAB_WIDTH * (col / TAB_WIDTH + 1);
            if (n > width) break;
            col = n;
        }
        else {
            break;
        }
    }

    return i;
}

static int
dedent_string(struct parser_params *p, rb_parser_string_t *string, int width)
{
    char *str;
    long len;
    int i;

    len = PARSER_STRING_LEN(string);
    str = PARSER_STRING_PTR(string);

    i = dedent_string_column(str, len, width);
    if (!i) return 0;

    rb_parser_str_modify(string);
    str = PARSER_STRING_PTR(string);
    if (PARSER_STRING_LEN(string) != len)
        rb_fatal("literal string changed: %s", PARSER_STRING_PTR(string));
    MEMMOVE(str, str + i, char, len - i);
    rb_parser_str_set_len(p, string, len - i);
    return i;
}

static NODE *
heredoc_dedent(struct parser_params *p, NODE *root)
{
    if (p->heredoc_indent <= 0) return root;
    YSTUB("heredoc_dedent");
    return root;
}

static int
whole_match_p(struct parser_params *p, const char *eos, long len, int indent)
{
    const char *beg = p->lex.pbeg;
    const char *ptr = p->lex.pend;

    if (ptr - beg < len) return FALSE;
    if (ptr > beg && ptr[-1] == '\n') {
        if (--ptr > beg && ptr[-1] == '\r') --ptr;
        if (ptr - beg < len) return FALSE;
    }
    if (strncmp(eos, ptr -= len, len)) return FALSE;
    if (indent) {
        while (beg < ptr && ISSPACE(*beg)) beg++;
    }
    return beg == ptr;
}

static int
word_match_p(struct parser_params *p, const char *word, long len)
{
    if (strncmp(p->lex.pcur, word, len)) return 0;
    if (lex_eol_n_p(p, len)) return 1;
    int c = (unsigned char)p->lex.pcur[len];
    if (ISSPACE(c)) return 1;
    switch (c) {
      case '\0': case '\004': case '\032': return 1;
    }
    return 0;
}

#define NUM_SUFFIX_R   (1<<0)
#define NUM_SUFFIX_I   (1<<1)
#define NUM_SUFFIX_ALL 3

static int
number_literal_suffix(struct parser_params *p, int mask)
{
    int c, result = 0;
    const char *lastp = p->lex.pcur;

    while ((c = nextc(p)) != -1) {
        if ((mask & NUM_SUFFIX_I) && c == 'i') {
            result |= (mask & NUM_SUFFIX_I);
            mask &= ~NUM_SUFFIX_I;
            /* r after i, rational of complex is disallowed */
            mask &= ~NUM_SUFFIX_R;
            continue;
        }
        if ((mask & NUM_SUFFIX_R) && c == 'r') {
            result |= (mask & NUM_SUFFIX_R);
            mask &= ~NUM_SUFFIX_R;
            continue;
        }
        if (!ISASCII(c) || ISALPHA(c) || c == '_') {
            p->lex.pcur = lastp;
            return 0;
        }
        pushback(p, c);
        break;
    }
    return result;
}

static enum yytokentype
set_number_literal(struct parser_params *p, enum yytokentype type, int suffix, int base, int seen_point)
{
    enum rb_numeric_type numeric_type = integer_literal;

    if (type == tFLOAT) {
        numeric_type = float_literal;
    }

    if (suffix & NUM_SUFFIX_R) {
        type = tRATIONAL;
        numeric_type = rational_literal;
    }
    if (suffix & NUM_SUFFIX_I) {
        type = tIMAGINARY;
    }

    switch (type) {
      case tINTEGER:
        set_yylval_node(NEW_INTEGER(strdup(tok(p)), base, &_cur_loc));
        break;
      case tFLOAT:
        set_yylval_node(NEW_FLOAT(strdup(tok(p)), &_cur_loc));
        break;
      case tRATIONAL:
        set_yylval_node(NEW_RATIONAL(strdup(tok(p)), base, seen_point, &_cur_loc));
        break;
      case tIMAGINARY:
        set_yylval_node(NEW_IMAGINARY(strdup(tok(p)), base, seen_point, numeric_type, &_cur_loc));
        (void)numeric_type;     /* for ripper */
        break;
      default:
        rb_bug("unexpected token: %d", type);
    }
    SET_LEX_STATE(EXPR_END);
    return type;
}


static enum yytokentype
here_document(struct parser_params *p, rb_strterm_heredoc_t *here)
{
    int c, func, indent = 0;
    const char *eos, *ptr, *ptr_end;
    long len;
    rb_parser_string_t *str = 0;
    rb_encoding *enc = p->enc;
    rb_encoding *base_enc = 0;
    int bol;

    eos = PARSER_STRING_PTR(here->lastline) + here->offset;
    len = here->length;
    indent = (func = here->func) & STR_FUNC_INDENT;

    if ((c = nextc(p)) == -1) {
      error:
        heredoc_restore(p, &p->lex.strterm->u.heredoc);
        compile_error(p, "can't find string \"%.*s\" anywhere before EOF",
                      (int)len, eos);
        token_flush(p);
        SET_LEX_STATE(EXPR_END);
        return tSTRING_END;
    }
    bol = was_bol(p);
    if (!bol) {
        /* not beginning of line, cannot be the terminator */
    }
    else if (p->heredoc_line_indent == -1) {
        /* `heredoc_line_indent == -1` means
         * - "after an interpolation in the same line", or
         * - "in a continuing line"
         */
        p->heredoc_line_indent = 0;
    }
    else if (whole_match_p(p, eos, len, indent)) {
        dispatch_heredoc_end(p);
      restore:
        heredoc_restore(p, &p->lex.strterm->u.heredoc);
        token_flush(p);
        SET_LEX_STATE(EXPR_END);
        return tSTRING_END;
    }

    if (!(func & STR_FUNC_EXPAND)) {
        do {
            ptr = PARSER_STRING_PTR(p->lex.lastline);
            ptr_end = p->lex.pend;
            if (ptr_end > ptr) {
                switch (ptr_end[-1]) {
                  case '\n':
                    if (--ptr_end == ptr || ptr_end[-1] != '\r') {
                        ptr_end++;
                        break;
                    }
                  case '\r':
                    --ptr_end;
                }
            }

            if (p->heredoc_indent > 0) {
                long i = 0;
                while (ptr + i < ptr_end && parser_update_heredoc_indent(p, ptr[i]))
                    i++;
                p->heredoc_line_indent = 0;
            }

            if (str)
                parser_str_cat(str, ptr, ptr_end - ptr);
            else
                str = rb_parser_encoding_string_new(p, ptr, ptr_end - ptr, enc);
            if (!lex_eol_ptr_p(p, ptr_end)) parser_str_cat_cstr(str, "\n");
            lex_goto_eol(p);
            if (p->heredoc_indent > 0) {
                goto flush_str;
            }
            if (nextc(p) == -1) {
                if (str) {
                    rb_parser_string_free(p, str);
                    str = 0;
                }
                goto error;
            }
        } while (!whole_match_p(p, eos, len, indent));
    }
    else {
        /*	int mb = ENC_CODERANGE_7BIT, *mbp = &mb;*/
        newtok(p);
        if (c == '#') {
            enum yytokentype t = parser_peek_variable_name(p);
            if (p->heredoc_line_indent != -1) {
                if (p->heredoc_indent > p->heredoc_line_indent) {
                    p->heredoc_indent = p->heredoc_line_indent;
                }
                p->heredoc_line_indent = -1;
            }
            if (t) return t;
            tokadd(p, '#');
            c = nextc(p);
        }
        do {
            pushback(p, c);
            enc = p->enc;
            if ((c = tokadd_string(p, func, '\n', 0, NULL, &enc, &base_enc)) == -1) {
                if (p->eofp) goto error;
                goto restore;
            }
            if (c != '\n') {
                if (c == '\\') p->heredoc_line_indent = -1;
              flush:
                str = STR_NEW3(tok(p), toklen(p), enc, func);
              flush_str:
                set_yylval_str(str);
                if (bol) nd_set_fl_newline(yylval.node);
                flush_string_content(p, enc, 0);
                return tSTRING_CONTENT;
            }
            tokadd(p, nextc(p));
            if (p->heredoc_indent > 0) {
                lex_goto_eol(p);
                goto flush;
            }
            /*	    if (mbp && mb == ENC_CODERANGE_UNKNOWN) mbp = 0;*/
            if ((c = nextc(p)) == -1) goto error;
        } while (!whole_match_p(p, eos, len, indent));
        str = STR_NEW3(tok(p), toklen(p), enc, func);
    }
    dispatch_heredoc_end(p);
    heredoc_restore(p, &p->lex.strterm->u.heredoc);
    token_flush(p);
    p->lex.strterm = NEW_STRTERM(func | STR_FUNC_TERM, 0, 0);
    set_yylval_str(str);

    if (bol) nd_set_fl_newline(yylval.node);
    return tSTRING_CONTENT;
}

#include "lex.inc"

static int
arg_ambiguous(struct parser_params *p, char c)
{
    rb_warning1("ambiguous first argument; put parentheses or a space even after '%c' operator", WARN_I(c));
    return TRUE;
}

/* returns true value if formal argument error;
 * Qtrue, or error message if ripper */
static VALUE
formal_argument_error(struct parser_params *p, ID id)
{
    switch (id_type(id)) {
      case ID_LOCAL:
        break;
# define ERR(mesg) (yyerror0(mesg), Qtrue)
      case ID_CONST:
        return ERR("formal argument cannot be a constant");
      case ID_INSTANCE:
        return ERR("formal argument cannot be an instance variable");
      case ID_GLOBAL:
        return ERR("formal argument cannot be a global variable");
      case ID_CLASS:
        return ERR("formal argument cannot be a class variable");
      default:
        return ERR("formal argument must be local variable");
#undef ERR
    }
    shadowing_lvar(p, id);

    return Qfalse;
}

static int
lvar_defined(struct parser_params *p, ID id)
{
    return (dyna_in_block(p) && dvar_defined(p, id)) || local_id(p, id);
}

/* emacsen -*- hack */
static long
parser_encode_length(struct parser_params *p, const char *name, long len)
{
    long nlen;

    if (len > 5 && name[nlen = len - 5] == '-') {
        if (rb_memcicmp(name + nlen + 1, "unix", 4) == 0)
            return nlen;
    }
    if (len > 4 && name[nlen = len - 4] == '-') {
        if (rb_memcicmp(name + nlen + 1, "dos", 3) == 0)
            return nlen;
        if (rb_memcicmp(name + nlen + 1, "mac", 3) == 0 &&
            !(len == 8 && rb_memcicmp(name, "utf8-mac", len) == 0))
            /* exclude UTF8-MAC because the encoding named "UTF8" doesn't exist in Ruby */
            return nlen;
    }
    return len;
}

static void
parser_set_encode(struct parser_params *p, const char *name)
{
    const pm_encoding_t *enc = pm_encoding_find((const uint8_t *) name, (const uint8_t *) name + strlen(name));

    if (enc == NULL) {
        compile_error(p, "unknown encoding name: %s", name);
        return;
    }

    p->enc = enc;
    p->pm->encoding = enc;
    p->pm->encoding_changed = true;
    if (p->pm->encoding_changed_callback != NULL) p->pm->encoding_changed_callback(p->pm);
}

static bool
comment_at_top(struct parser_params *p)
{
    if (p->token_seen) return false;
    return (p->line_count == (p->has_shebang ? 2 : 1));
}

typedef long (*rb_magic_comment_length_t)(struct parser_params *p, const char *name, long len);
typedef void (*rb_magic_comment_setter_t)(struct parser_params *p, const char *name, const char *val);

static int parser_invalid_pragma_value(struct parser_params *p, const char *name, const char *val);

static void
magic_comment_encoding(struct parser_params *p, const char *name, const char *val)
{
    if (!comment_at_top(p)) {
        return;
    }
    parser_set_encode(p, val);
}

static int
parser_get_bool(struct parser_params *p, const char *name, const char *val)
{
    switch (*val) {
      case 't': case 'T':
        if (STRCASECMP(val, "true") == 0) {
            return TRUE;
        }
        break;
      case 'f': case 'F':
        if (STRCASECMP(val, "false") == 0) {
            return FALSE;
        }
        break;
    }
    return parser_invalid_pragma_value(p, name, val);
}

static int
parser_invalid_pragma_value(struct parser_params *p, const char *name, const char *val)
{
    rb_warning2("invalid value for %s: %s", WARN_S(name), WARN_S(val));
    return -1;
}

static void
parser_set_token_info(struct parser_params *p, const char *name, const char *val)
{
    int b = parser_get_bool(p, name, val);
    if (b >= 0) p->token_info_enabled = b;
}

static void
parser_set_frozen_string_literal(struct parser_params *p, const char *name, const char *val)
{
    int b;

    if (p->token_seen) {
        rb_warning1("'%s' is ignored after any tokens", WARN_S(name));
        return;
    }

    b = parser_get_bool(p, name, val);
    if (b < 0) return;

    p->frozen_string_literal = b;
}

static void
parser_set_shareable_constant_value(struct parser_params *p, const char *name, const char *val)
{
    for (const char *s = p->lex.pbeg, *e = p->lex.pcur; s < e; ++s) {
        if (*s == ' ' || *s == '\t') continue;
        if (*s == '#') break;
        rb_warning1("'%s' is ignored unless in comment-only line", WARN_S(name));
        return;
    }

    switch (*val) {
      case 'n': case 'N':
        if (STRCASECMP(val, "none") == 0) {
            p->ctxt.shareable_constant_value = rb_parser_shareable_none;
            return;
        }
        break;
      case 'l': case 'L':
        if (STRCASECMP(val, "literal") == 0) {
            p->ctxt.shareable_constant_value = rb_parser_shareable_literal;
            return;
        }
        break;
      case 'e': case 'E':
        if (STRCASECMP(val, "experimental_copy") == 0) {
            p->ctxt.shareable_constant_value = rb_parser_shareable_copy;
            return;
        }
        if (STRCASECMP(val, "experimental_everything") == 0) {
            p->ctxt.shareable_constant_value = rb_parser_shareable_everything;
            return;
        }
        break;
    }
    parser_invalid_pragma_value(p, name, val);
}

# if WARN_PAST_SCOPE
static void
parser_set_past_scope(struct parser_params *p, const char *name, const char *val)
{
    int b = parser_get_bool(p, name, val);
    if (b >= 0) p->past_scope_enabled = b;
}
# endif

struct magic_comment {
    const char *name;
    rb_magic_comment_setter_t func;
    rb_magic_comment_length_t length;
};

static const struct magic_comment magic_comments[] = {
    {"coding", magic_comment_encoding, parser_encode_length},
    {"encoding", magic_comment_encoding, parser_encode_length},
    {"frozen_string_literal", parser_set_frozen_string_literal},
    {"shareable_constant_value", parser_set_shareable_constant_value},
    {"warn_indent", parser_set_token_info},
# if WARN_PAST_SCOPE
    {"warn_past_scope", parser_set_past_scope},
# endif
};

static const char *
magic_comment_marker(const char *str, long len)
{
    long i = 2;

    while (i < len) {
        switch (str[i]) {
          case '-':
            if (str[i-1] == '*' && str[i-2] == '-') {
                return str + i + 1;
            }
            i += 2;
            break;
          case '*':
            if (i + 1 >= len) return 0;
            if (str[i+1] != '-') {
                i += 4;
            }
            else if (str[i-1] != '-') {
                i += 2;
            }
            else {
                return str + i + 2;
            }
            break;
          default:
            i += 3;
            break;
        }
    }
    return 0;
}

static int
parser_magic_comment(struct parser_params *p, const char *str, long len)
{
    int indicator = 0;
    rb_parser_string_t *name = 0, *val = 0;
    const char *beg, *end, *vbeg, *vend;
#define str_copy(_s, _p, _n) ((_s) \
        ? (void)(pm_ystring_resize((_s), (_n)), \
           MEMCPY(PM_YSTRING_PTR(_s), (_p), char, (_n)), (_s)) \
        : (void)((_s) = STR_NEW((_p), (_n))))

    if (len <= 7) return FALSE;
    if (!!(beg = magic_comment_marker(str, len))) {
        if (!(end = magic_comment_marker(beg, str + len - beg)))
            return FALSE;
        indicator = TRUE;
        str = beg;
        len = end - beg - 3;
    }

    /* %r"([^\\s\'\":;]+)\\s*:\\s*(\"(?:\\\\.|[^\"])*\"|[^\"\\s;]+)[\\s;]*" */
    while (len > 0) {
        const struct magic_comment *mc = magic_comments;
        char *s;
        int i;
        long n = 0;

        for (; len > 0 && *str; str++, --len) {
            switch (*str) {
              case '\'': case '"': case ':': case ';':
                continue;
            }
            if (!ISSPACE(*str)) break;
        }
        for (beg = str; len > 0; str++, --len) {
            switch (*str) {
              case '\'': case '"': case ':': case ';':
                break;
              default:
                if (ISSPACE(*str)) break;
                continue;
            }
            break;
        }
        for (end = str; len > 0 && ISSPACE(*str); str++, --len);
        if (!len) break;
        if (*str != ':') {
            if (!indicator) return FALSE;
            continue;
        }

        do str++; while (--len > 0 && ISSPACE(*str));
        if (!len) break;
        const char *tok_beg = str;
        if (*str == '"') {
            for (vbeg = ++str; --len > 0 && *str != '"'; str++) {
                if (*str == '\\') {
                    --len;
                    ++str;
                }
            }
            vend = str;
            if (len) {
                --len;
                ++str;
            }
        }
        else {
            for (vbeg = str; len > 0 && *str != '"' && *str != ';' && !ISSPACE(*str); --len, str++);
            vend = str;
        }
        const char *tok_end = str;
        if (indicator) {
            while (len > 0 && (*str == ';' || ISSPACE(*str))) --len, str++;
        }
        else {
            while (len > 0 && (ISSPACE(*str))) --len, str++;
            if (len) {
                pm_ystring_free(name);
                pm_ystring_free(val);
                return FALSE;
            }
        }

        n = end - beg;
        str_copy(name, beg, n);
        s = PM_YSTRING_PTR(name);
        for (i = 0; i < n; ++i) {
            if (s[i] == '-') s[i] = '_';
        }
        do {
            if (STRNCASECMP(mc->name, s, n) == 0 && !mc->name[n]) {
                n = vend - vbeg;
                if (mc->length) {
                    n = (*mc->length)(p, vbeg, n);
                }
                str_copy(val, vbeg, n);
                p->lex.ptok = tok_beg;
                p->lex.pcur = tok_end;
                (*mc->func)(p, mc->name, PM_YSTRING_PTR(val));
                break;
            }
        } while (++mc < magic_comments + numberof(magic_comments));
    }

    pm_ystring_free(name);
    pm_ystring_free(val);
    return TRUE;
}

static void
set_file_encoding(struct parser_params *p, const char *str, const char *send)
{
    int sep = 0;
    const char *beg = str;
    rb_parser_string_t *s;

    for (;;) {
        if (send - str <= 6) return;
        switch (str[6]) {
          case 'C': case 'c': str += 6; continue;
          case 'O': case 'o': str += 5; continue;
          case 'D': case 'd': str += 4; continue;
          case 'I': case 'i': str += 3; continue;
          case 'N': case 'n': str += 2; continue;
          case 'G': case 'g': str += 1; continue;
          case '=': case ':':
            sep = 1;
            str += 6;
            break;
          default:
            str += 6;
            if (ISSPACE(*str)) break;
            continue;
        }
        if (STRNCASECMP(str-6, "coding", 6) == 0) break;
        sep = 0;
    }
    for (;;) {
        do {
            if (++str >= send) return;
        } while (ISSPACE(*str));
        if (sep) break;
        if (*str != '=' && *str != ':') return;
        sep = 1;
        str++;
    }
    beg = str;
    while ((*str == '-' || *str == '_' || ISALNUM(*str)) && ++str < send);
    s = rb_parser_string_new(p, beg, parser_encode_length(p, beg, str - beg));
    p->lex.ptok = beg;
    p->lex.pcur = str;
    parser_set_encode(p, PM_YSTRING_PTR(s));
    pm_ystring_free(s);
}

static void
parser_prepare(struct parser_params *p)
{
    int c = nextc0(p, FALSE);
    p->token_info_enabled = !compile_for_eval && RTEST(ruby_verbose);
    switch (c) {
      case '#':
        if (peek(p, '!')) p->has_shebang = 1;
        break;
      case 0xef:		/* UTF-8 BOM marker */
        if (!lex_eol_n_p(p, 2) &&
            (unsigned char)p->lex.pcur[0] == 0xbb &&
            (unsigned char)p->lex.pcur[1] == 0xbf) {
            p->enc = rb_utf8_encoding();
            p->lex.pcur += 2;
            p->lex.pbeg = p->lex.pcur;
            token_flush(p);
            return;
        }
        break;
      case -1:   /* end of script. */
        return;
    }
    pushback(p, c);
    p->enc = rb_parser_str_get_encoding(p->lex.lastline);
}

#define ambiguous_operator(tok, op, syn) ( \
    rb_warning0("'"op"' after local variable or literal is interpreted as binary operator"), \
    rb_warning0("even though it seems like "syn""))
#define warn_balanced(tok, op, syn) ((void) \
    (!IS_lex_state_for(last_state, EXPR_CLASS|EXPR_DOT|EXPR_FNAME|EXPR_ENDFN) && \
     space_seen && !ISSPACE(c) && \
     (ambiguous_operator(tok, op, syn), 0)), \
     (enum yytokentype)(tok))

static enum yytokentype
no_digits(struct parser_params *p)
{
    yyerror0("numeric literal without digits");
    if (peek(p, '_')) nextc(p);
    /* dummy 0, for tUMINUS_NUM at numeric */
    return set_number_literal(p, tINTEGER, 0, 10, 0);
}

static enum yytokentype
parse_numeric(struct parser_params *p, int c)
{
    int is_float, seen_point, seen_e, nondigit;
    int suffix;

    is_float = seen_point = seen_e = nondigit = 0;
    SET_LEX_STATE(EXPR_END);
    newtok(p);
    if (c == '-' || c == '+') {
        tokadd(p, c);
        c = nextc(p);
    }
    if (c == '0') {
        int start = toklen(p);
        c = nextc(p);
        if (c == 'x' || c == 'X') {
            /* hexadecimal */
            c = nextc(p);
            if (c != -1 && ISXDIGIT(c)) {
                do {
                    if (c == '_') {
                        if (nondigit) break;
                        nondigit = c;
                        continue;
                    }
                    if (!ISXDIGIT(c)) break;
                    nondigit = 0;
                    tokadd(p, c);
                } while ((c = nextc(p)) != -1);
            }
            pushback(p, c);
            tokfix(p);
            if (toklen(p) == start) {
                return no_digits(p);
            }
            else if (nondigit) goto trailing_uc;
            suffix = number_literal_suffix(p, NUM_SUFFIX_ALL);
            return set_number_literal(p, tINTEGER, suffix, 16, 0);
        }
        if (c == 'b' || c == 'B') {
            /* binary */
            c = nextc(p);
            if (c == '0' || c == '1') {
                do {
                    if (c == '_') {
                        if (nondigit) break;
                        nondigit = c;
                        continue;
                    }
                    if (c != '0' && c != '1') break;
                    nondigit = 0;
                    tokadd(p, c);
                } while ((c = nextc(p)) != -1);
            }
            pushback(p, c);
            tokfix(p);
            if (toklen(p) == start) {
                return no_digits(p);
            }
            else if (nondigit) goto trailing_uc;
            suffix = number_literal_suffix(p, NUM_SUFFIX_ALL);
            return set_number_literal(p, tINTEGER, suffix, 2, 0);
        }
        if (c == 'd' || c == 'D') {
            /* decimal */
            c = nextc(p);
            if (c != -1 && ISDIGIT(c)) {
                do {
                    if (c == '_') {
                        if (nondigit) break;
                        nondigit = c;
                        continue;
                    }
                    if (!ISDIGIT(c)) break;
                    nondigit = 0;
                    tokadd(p, c);
                } while ((c = nextc(p)) != -1);
            }
            pushback(p, c);
            tokfix(p);
            if (toklen(p) == start) {
                return no_digits(p);
            }
            else if (nondigit) goto trailing_uc;
            suffix = number_literal_suffix(p, NUM_SUFFIX_ALL);
            return set_number_literal(p, tINTEGER, suffix, 10, 0);
        }
        if (c == '_') {
            /* 0_0 */
            goto octal_number;
        }
        if (c == 'o' || c == 'O') {
            /* prefixed octal */
            c = nextc(p);
            if (c == -1 || c == '_' || !ISDIGIT(c)) {
                tokfix(p);
                return no_digits(p);
            }
        }
        if (c >= '0' && c <= '7') {
            /* octal */
          octal_number:
            do {
                if (c == '_') {
                    if (nondigit) break;
                    nondigit = c;
                    continue;
                }
                if (c < '0' || c > '9') break;
                if (c > '7') goto invalid_octal;
                nondigit = 0;
                tokadd(p, c);
            } while ((c = nextc(p)) != -1);
            if (toklen(p) > start) {
                pushback(p, c);
                tokfix(p);
                if (nondigit) goto trailing_uc;
                suffix = number_literal_suffix(p, NUM_SUFFIX_ALL);
                return set_number_literal(p, tINTEGER, suffix, 8, 0);
            }
            if (nondigit) {
                pushback(p, c);
                goto trailing_uc;
            }
        }
        if (c > '7' && c <= '9') {
          invalid_octal:
            yyerror0("Invalid octal digit");
        }
        else if (c == '.' || c == 'e' || c == 'E') {
            tokadd(p, '0');
        }
        else {
            pushback(p, c);
            tokfix(p);
            suffix = number_literal_suffix(p, NUM_SUFFIX_ALL);
            return set_number_literal(p, tINTEGER, suffix, 10, 0);
        }
    }

    for (;;) {
        switch (c) {
          case '0': case '1': case '2': case '3': case '4':
          case '5': case '6': case '7': case '8': case '9':
            nondigit = 0;
            tokadd(p, c);
            break;

          case '.':
            if (nondigit) goto trailing_uc;
            if (seen_point || seen_e) {
                goto decode_num;
            }
            else {
                int c0 = nextc(p);
                if (c0 == -1 || !ISDIGIT(c0)) {
                    pushback(p, c0);
                    goto decode_num;
                }
                c = c0;
            }
            seen_point = toklen(p);
            tokadd(p, '.');
            tokadd(p, c);
            is_float++;
            nondigit = 0;
            break;

          case 'e':
          case 'E':
            if (nondigit) {
                pushback(p, c);
                c = nondigit;
                goto decode_num;
            }
            if (seen_e) {
                goto decode_num;
            }
            nondigit = c;
            c = nextc(p);
            if (c != '-' && c != '+' && !ISDIGIT(c)) {
                pushback(p, c);
                c = nondigit;
                nondigit = 0;
                goto decode_num;
            }
            tokadd(p, nondigit);
            seen_e++;
            is_float++;
            tokadd(p, c);
            nondigit = (c == '-' || c == '+') ? c : 0;
            break;

          case '_':	/* `_' in number just ignored */
            if (nondigit) goto decode_num;
            nondigit = c;
            break;

          default:
            goto decode_num;
        }
        c = nextc(p);
    }

  decode_num:
    pushback(p, c);
    if (nondigit) {
      trailing_uc:
        literal_flush(p, p->lex.pcur - 1);
        YYLTYPE loc = RUBY_INIT_YYLLOC();
        compile_error(p, "trailing '%c' in number", nondigit);
        parser_show_error_line(p, &loc);
    }
    tokfix(p);
    if (is_float) {
        enum yytokentype type = tFLOAT;

        suffix = number_literal_suffix(p, seen_e ? NUM_SUFFIX_I : NUM_SUFFIX_ALL);
        if (suffix & NUM_SUFFIX_R) {
            type = tRATIONAL;
        }
        else {
            strtod(tok(p), 0);
            if (errno == ERANGE) {
                rb_warning1("Float %s out of range", WARN_S(tok(p)));
                errno = 0;
            }
        }
        return set_number_literal(p, type, suffix, 0, seen_point);
    }
    suffix = number_literal_suffix(p, NUM_SUFFIX_ALL);
    return set_number_literal(p, tINTEGER, suffix, 10, 0);
}

static enum yytokentype
parse_qmark(struct parser_params *p, int space_seen)
{
    rb_encoding *enc;
    register int c;
    rb_parser_string_t *lit;
    const char *start = p->lex.pcur;

    if (IS_END()) {
        SET_LEX_STATE(EXPR_VALUE);
        return '?';
    }
    c = nextc(p);
    if (c == -1) {
        compile_error(p, "incomplete character syntax");
        return 0;
    }
    if (rb_enc_isspace(c, p->enc)) {
        if (!IS_ARG()) {
            int c2 = escaped_control_code(c);
            if (c2) {
                WARN_SPACE_CHAR(c2, "?");
            }
        }
      ternary:
        pushback(p, c);
        SET_LEX_STATE(EXPR_VALUE);
        return '?';
    }
    newtok(p);
    enc = p->enc;
    int w = parser_precise_mbclen(p, start);
    if (is_identchar(p, start, p->lex.pend, p->enc) &&
        !(lex_eol_ptr_n_p(p, start, w) || !is_identchar(p, start + w, p->lex.pend, p->enc))) {
        if (space_seen) {
            const char *ptr = start;
            do {
                int n = parser_precise_mbclen(p, ptr);
                if (n < 0) return -1;
                ptr += n;
            } while (!lex_eol_ptr_p(p, ptr) && is_identchar(p, ptr, p->lex.pend, p->enc));
            rb_warn2("'?' just followed by '%.*s' is interpreted as" \
                     " a conditional operator, put a space after '?'",
                     WARN_I((int)(ptr - start)), WARN_S_L(start, (ptr - start)));
        }
        goto ternary;
    }
    else if (c == '\\') {
        if (peek(p, 'u')) {
            nextc(p);
            enc = rb_utf8_encoding();
            tokadd_utf8(p, &enc, -1, 0, 0);
        }
        else if (!ISASCII(c = peekc(p)) && c != -1) {
            nextc(p);
            if (tokadd_mbchar(p, c) == -1) return 0;
        }
        else {
            c = read_escape(p, 0, p->lex.pcur - rb_strlen_lit("?\\"));
            tokadd(p, c);
        }
    }
    else {
        if (tokadd_mbchar(p, c) == -1) return 0;
    }
    tokfix(p);
    lit = STR_NEW3(tok(p), toklen(p), enc, 0);
    set_yylval_str(lit);
    SET_LEX_STATE(EXPR_END);
    return tCHAR;
}

static enum yytokentype
parse_percent(struct parser_params *p, const int space_seen, const enum lex_state_e last_state)
{
    register int c;
    const char *ptok = p->lex.pcur;

    if (IS_BEG()) {
        int term;
        int paren;

        c = nextc(p);
      quotation:
        if (c == -1) goto unterminated;
        if (!ISALNUM(c)) {
            term = c;
            if (!ISASCII(c)) goto unknown;
            c = 'Q';
        }
        else {
            term = nextc(p);
            if (rb_enc_isalnum(term, p->enc) || !parser_isascii(p)) {
              unknown:
                pushback(p, term);
                c = parser_precise_mbclen(p, p->lex.pcur);
                if (c < 0) return 0;
                p->lex.pcur += c;
                yyerror0("unknown type of %string");
                return 0;
            }
        }
        if (term == -1) {
          unterminated:
            compile_error(p, "unterminated quoted string meets end of file");
            return 0;
        }
        paren = term;
        if (term == '(') term = ')';
        else if (term == '[') term = ']';
        else if (term == '{') term = '}';
        else if (term == '<') term = '>';
        else paren = 0;

        p->lex.ptok = ptok-1;
        switch (c) {
          case 'Q':
            p->lex.strterm = NEW_STRTERM(str_dquote, term, paren);
            return tSTRING_BEG;

          case 'q':
            p->lex.strterm = NEW_STRTERM(str_squote, term, paren);
            return tSTRING_BEG;

          case 'W':
            p->lex.strterm = NEW_STRTERM(str_dword, term, paren);
            return tWORDS_BEG;

          case 'w':
            p->lex.strterm = NEW_STRTERM(str_sword, term, paren);
            return tQWORDS_BEG;

          case 'I':
            p->lex.strterm = NEW_STRTERM(str_dword, term, paren);
            return tSYMBOLS_BEG;

          case 'i':
            p->lex.strterm = NEW_STRTERM(str_sword, term, paren);
            return tQSYMBOLS_BEG;

          case 'x':
            p->lex.strterm = NEW_STRTERM(str_xquote, term, paren);
            return tXSTRING_BEG;

          case 'r':
            p->lex.strterm = NEW_STRTERM(str_regexp, term, paren);
            return tREGEXP_BEG;

          case 's':
            p->lex.strterm = NEW_STRTERM(str_ssym, term, paren);
            SET_LEX_STATE(EXPR_FNAME|EXPR_FITEM);
            return tSYMBEG;

          default:
            yyerror0("unknown type of %string");
            return 0;
        }
    }
    if ((c = nextc(p)) == '=') {
        set_yylval_id('%');
        SET_LEX_STATE(EXPR_BEG);
        return tOP_ASGN;
    }
    if (IS_SPCARG(c) || (IS_lex_state(EXPR_FITEM) && c == 's')) {
        goto quotation;
    }
    SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
    pushback(p, c);
    return warn_balanced('%', "%%", "string literal");
}

static int
tokadd_ident(struct parser_params *p, int c)
{
    do {
        if (tokadd_mbchar(p, c) == -1) return -1;
        c = nextc(p);
    } while (parser_is_identchar(p));
    pushback(p, c);
    return 0;
}

static ID
tokenize_ident(struct parser_params *p)
{
    ID ident = TOK_INTERN();

    set_yylval_name(ident);

    return ident;
}

static int
parse_numvar(struct parser_params *p)
{
    size_t len;
    int overflow;
    unsigned long n = ruby_scan_digits(tok(p)+1, toklen(p)-1, 10, &len, &overflow);
    const unsigned long nth_ref_max =
        ((FIXNUM_MAX < INT_MAX) ? FIXNUM_MAX : INT_MAX) >> 1;
    /* NTH_REF is left-shifted to be ORed with back-ref flag and
     * turned into a Fixnum, in compile.c */

    if (overflow || n > nth_ref_max) {
        /* compile_error()? */
        rb_warn1("'%s' is too big for a number variable, always nil", WARN_S(tok(p)));
        return 0;		/* $0 is $PROGRAM_NAME, not NTH_REF */
    }
    else {
        return (int)n;
    }
}

static enum yytokentype
parse_gvar(struct parser_params *p, const enum lex_state_e last_state)
{
    const char *ptr = p->lex.pcur;
    register int c;

    SET_LEX_STATE(EXPR_END);
    p->lex.ptok = ptr - 1; /* from '$' */
    newtok(p);
    c = nextc(p);
    switch (c) {
      case '_':		/* $_: last read line string */
        c = nextc(p);
        if (parser_is_identchar(p)) {
            tokadd(p, '$');
            tokadd(p, '_');
            break;
        }
        pushback(p, c);
        c = '_';
        /* fall through */
      case '~': 	/* $~: match-data */
      case '*': 	/* $*: argv */
      case '$': 	/* $$: pid */
      case '?': 	/* $?: last status */
      case '!': 	/* $!: error string */
      case '@': 	/* $@: error position */
      case '/': 	/* $/: input record separator */
      case '\\':	/* $\: output record separator */
      case ';': 	/* $;: field separator */
      case ',': 	/* $,: output field separator */
      case '.': 	/* $.: last read line number */
      case '=': 	/* $=: ignorecase */
      case ':': 	/* $:: load path */
      case '<': 	/* $<: default input handle */
      case '>': 	/* $>: default output handle */
      case '\"':	/* $": already loaded files */
        tokadd(p, '$');
        tokadd(p, c);
        goto gvar;

      case '-':
        tokadd(p, '$');
        tokadd(p, c);
        c = nextc(p);
        if (parser_is_identchar(p)) {
            if (tokadd_mbchar(p, c) == -1) return 0;
        }
        else {
            pushback(p, c);
            pushback(p, '-');
            return '$';
        }
      gvar:
        tokenize_ident(p);
        return tGVAR;

      case '&': 	/* $&: last match */
      case '`': 	/* $`: string before last match */
      case '\'':	/* $': string after last match */
      case '+': 	/* $+: string matches last paren. */
        if (IS_lex_state_for(last_state, EXPR_FNAME)) {
            tokadd(p, '$');
            tokadd(p, c);
            goto gvar;
        }
        set_yylval_node(NEW_BACK_REF(c, &_cur_loc));
        return tBACK_REF;

      case '1': case '2': case '3':
      case '4': case '5': case '6':
      case '7': case '8': case '9':
        tokadd(p, '$');
        do {
            tokadd(p, c);
            c = nextc(p);
        } while (c != -1 && ISDIGIT(c));
        pushback(p, c);
        if (IS_lex_state_for(last_state, EXPR_FNAME)) goto gvar;
        tokfix(p);
        c = parse_numvar(p);
        set_yylval_node(NEW_NTH_REF(c, &_cur_loc));
        return tNTH_REF;

      default:
        if (!parser_is_identchar(p)) {
            YYLTYPE loc = RUBY_INIT_YYLLOC();
            if (c == -1 || ISSPACE(c)) {
                compile_error(p, "'$' without identifiers is not allowed as a global variable name");
            }
            else {
                pushback(p, c);
                compile_error(p, "'$%c' is not allowed as a global variable name", c);
            }
            parser_show_error_line(p, &loc);
            set_yylval_noname();
            return tGVAR;
        }
        /* fall through */
      case '0':
        tokadd(p, '$');
    }

    if (tokadd_ident(p, c)) return 0;
    SET_LEX_STATE(EXPR_END);
    if (VALID_SYMNAME_P(tok(p), toklen(p), p->enc, ID_GLOBAL)) {
        tokenize_ident(p);
    }
    else {
        compile_error(p, "'%.*s' is not allowed as a global variable name", toklen(p), tok(p));
        set_yylval_noname();
    }
    return tGVAR;
}

static bool
parser_numbered_param(struct parser_params *p, int n)
{
    if (n < 0) return false;

    if (DVARS_TERMINAL_P(p->lvtbl->args) || DVARS_TERMINAL_P(p->lvtbl->args->prev)) {
        return false;
    }
    if (p->max_numparam == ORDINAL_PARAM) {
        compile_error(p, "ordinary parameter is defined");
        return false;
    }
    struct vtable *args = p->lvtbl->args;
    if (p->max_numparam < n) {
        p->max_numparam = n;
    }
    while (n > args->pos) {
        vtable_add(args, NUMPARAM_IDX_TO_ID(args->pos+1));
    }
    return true;
}

static enum yytokentype
parse_atmark(struct parser_params *p, const enum lex_state_e last_state)
{
    const char *ptr = p->lex.pcur;
    enum yytokentype result = tIVAR;
    register int c = nextc(p);
    YYLTYPE loc;

    p->lex.ptok = ptr - 1; /* from '@' */
    newtok(p);
    tokadd(p, '@');
    if (c == '@') {
        result = tCVAR;
        tokadd(p, '@');
        c = nextc(p);
    }
    SET_LEX_STATE(IS_lex_state_for(last_state, EXPR_FNAME) ? EXPR_ENDFN : EXPR_END);
    if (c == -1 || !parser_is_identchar(p)) {
        pushback(p, c);
        RUBY_SET_YYLLOC(loc);
        if (result == tIVAR) {
            compile_error(p, "'@' without identifiers is not allowed as an instance variable name");
        }
        else {
            compile_error(p, "'@@' without identifiers is not allowed as a class variable name");
        }
        parser_show_error_line(p, &loc);
        set_yylval_noname();
        SET_LEX_STATE(EXPR_END);
        return result;
    }
    else if (ISDIGIT(c)) {
        pushback(p, c);
        RUBY_SET_YYLLOC(loc);
        if (result == tIVAR) {
            compile_error(p, "'@%c' is not allowed as an instance variable name", c);
        }
        else {
            compile_error(p, "'@@%c' is not allowed as a class variable name", c);
        }
        parser_show_error_line(p, &loc);
        set_yylval_noname();
        SET_LEX_STATE(EXPR_END);
        return result;
    }

    if (tokadd_ident(p, c)) return 0;
    tokenize_ident(p);
    return result;
}

static enum yytokentype
parse_ident(struct parser_params *p, int c, int cmd_state)
{
    enum yytokentype result;
    bool is_ascii = true;
    const enum lex_state_e last_state = p->lex.state;
    ID ident;
    int enforce_keyword_end = 0;

    do {
        if (!ISASCII(c)) is_ascii = false;
        if (tokadd_mbchar(p, c) == -1) return 0;
        c = nextc(p);
    } while (parser_is_identchar(p));
    if ((c == '!' || c == '?') && !peek(p, '=')) {
        result = tFID;
        tokadd(p, c);
    }
    else if (c == '=' && IS_lex_state(EXPR_FNAME) &&
             (!peek(p, '~') && !peek(p, '>') && (!peek(p, '=') || (peek_n(p, '>', 1))))) {
        result = tIDENTIFIER;
        tokadd(p, c);
    }
    else {
        result = tCONSTANT;	/* assume provisionally */
        pushback(p, c);
    }
    tokfix(p);

    if (IS_LABEL_POSSIBLE()) {
        if (IS_LABEL_SUFFIX(0)) {
            SET_LEX_STATE(EXPR_ARG|EXPR_LABELED);
            nextc(p);
            tokenize_ident(p);
            return tLABEL;
        }
    }

    if (peek_end_expect_token_locations(p)) {
        const rb_code_position_t *end_pos;
        int lineno, column;
        int beg_pos = (int)(p->lex.ptok - p->lex.pbeg);

        end_pos = peek_end_expect_token_locations(p)->pos;
        lineno = end_pos->lineno;
        column = end_pos->column;

        if (p->debug) {
            rb_parser_printf(p, "enforce_keyword_end check. current: (%d, %d), peek: (%d, %d)\n",
                                p->ruby_sourceline, beg_pos, lineno, column);
        }

        if ((p->ruby_sourceline > lineno) && (beg_pos <= column)) {
            const struct kwtable *kw;

            if ((IS_lex_state(EXPR_DOT)) && (kw = rb_reserved_word(tok(p), toklen(p))) && (kw && kw->id[0] == keyword_end)) {
                if (p->debug) rb_parser_printf(p, "enforce_keyword_end is enabled\n");
                enforce_keyword_end = 1;
            }
        }
    }

    if (is_ascii && (!IS_lex_state(EXPR_DOT) || enforce_keyword_end)) {
        const struct kwtable *kw;

        /* See if it is a reserved word.  */
        kw = rb_reserved_word(tok(p), toklen(p));
        if (kw) {
            enum lex_state_e state = p->lex.state;
            if (IS_lex_state_for(state, EXPR_FNAME)) {
                SET_LEX_STATE(EXPR_ENDFN);
                set_yylval_name(rb_intern2(tok(p), toklen(p)));
                return kw->id[0];
            }
            SET_LEX_STATE(kw->state);
            if (IS_lex_state(EXPR_BEG)) {
                p->command_start = TRUE;
            }
            if (kw->id[0] == keyword_do) {
                if (lambda_beginning_p()) {
                    p->lex.lpar_beg = -1; /* make lambda_beginning_p() == FALSE in the body of "-> do ... end" */
                    return keyword_do_LAMBDA;
                }
                if (COND_P()) return keyword_do_cond;
                if (CMDARG_P() && !IS_lex_state_for(state, EXPR_CMDARG))
                    return keyword_do_block;
                return keyword_do;
            }
            if (IS_lex_state_for(state, (EXPR_BEG | EXPR_LABELED | EXPR_CLASS)))
                return kw->id[0];
            else {
                if (kw->id[0] != kw->id[1])
                    SET_LEX_STATE(EXPR_BEG | EXPR_LABEL);
                return kw->id[1];
            }
        }
    }

    if (IS_lex_state(EXPR_BEG_ANY | EXPR_ARG_ANY | EXPR_DOT)) {
        if (cmd_state) {
            SET_LEX_STATE(EXPR_CMDARG);
        }
        else {
            SET_LEX_STATE(EXPR_ARG);
        }
    }
    else if (p->lex.state == EXPR_FNAME) {
        SET_LEX_STATE(EXPR_ENDFN);
    }
    else {
        SET_LEX_STATE(EXPR_END);
    }

    ident = tokenize_ident(p);
    if (result == tCONSTANT && is_local_id(ident)) result = tIDENTIFIER;
    if (!IS_lex_state_for(last_state, EXPR_DOT|EXPR_FNAME) &&
        (result == tIDENTIFIER) && /* not EXPR_FNAME, not attrasgn */
        (lvar_defined(p, ident) || NUMPARAM_ID_P(ident))) {
        SET_LEX_STATE(EXPR_END|EXPR_LABEL);
    }
    return result;
}

static void
warn_cr(struct parser_params *p)
{
    if (!p->cr_seen) {
        p->cr_seen = TRUE;
        /* carried over with p->lex.nextline for nextc() */
        rb_warn0("encountered \\r in middle of line, treated as a mere space");
    }
}

static enum yytokentype
parser_yylex(struct parser_params *p)
{
    register int c;
    int space_seen = 0;
    int cmd_state;
    int label;
    enum lex_state_e last_state;
    int fallthru = FALSE;
    int token_seen = p->token_seen;

    if (p->lex.strterm) {
        if (strterm_is_heredoc(p->lex.strterm)) {
            token_flush(p);
            return here_document(p, &p->lex.strterm->u.heredoc);
        }
        else {
            token_flush(p);
            return parse_string(p, &p->lex.strterm->u.literal);
        }
    }
    cmd_state = p->command_start;
    p->command_start = FALSE;
    p->token_seen = TRUE;
    token_flush(p);
  retry:
    last_state = p->lex.state;
    switch (c = nextc(p)) {
      case '\0':		/* NUL */
      case '\004':		/* ^D */
      case '\032':		/* ^Z */
      case -1:			/* end of script. */
        p->eofp = 1;
        /* Set location for end-of-input because dispatch_scan_event is not called. */
        RUBY_SET_YYLLOC(*p->yylloc);
        return END_OF_INPUT;

        /* white spaces */
      case '\r':
        warn_cr(p);
        /* fall through */
      case ' ': case '\t': case '\f':
      case '\13': /* '\v' */
        space_seen = 1;
        while ((c = nextc(p))) {
            switch (c) {
              case '\r':
                warn_cr(p);
                /* fall through */
              case ' ': case '\t': case '\f':
              case '\13': /* '\v' */
                break;
              default:
                goto outofloop;
            }
        }
      outofloop:
        pushback(p, c);
        dispatch_scan_event(p, tSP);
        token_flush(p);
        goto retry;

      case '#':		/* it's a comment */
        p->token_seen = token_seen;
        const char *const pcur = p->lex.pcur, *const ptok = p->lex.ptok;
        /* no magic_comment in shebang line */
        if (!parser_magic_comment(p, p->lex.pcur, p->lex.pend - p->lex.pcur)) {
            if (comment_at_top(p)) {
                set_file_encoding(p, p->lex.pcur, p->lex.pend);
            }
        }
        p->lex.pcur = pcur, p->lex.ptok = ptok;
        lex_goto_eol(p);
        dispatch_scan_event(p, tCOMMENT);
        fallthru = TRUE;
        /* fall through */
      case '\n':
        p->token_seen = token_seen;
        rb_parser_string_t *prevline = p->lex.lastline;
        c = (IS_lex_state(EXPR_BEG|EXPR_CLASS|EXPR_FNAME|EXPR_DOT) &&
             !IS_lex_state(EXPR_LABELED));
        if (c || IS_lex_state_all(EXPR_ARG|EXPR_LABELED)) {
            if (!fallthru) {
                dispatch_scan_event(p, tIGNORED_NL);
            }
            fallthru = FALSE;
            if (!c && p->ctxt.in_kwarg) {
                goto normal_newline;
            }
            goto retry;
        }
        while (1) {
            switch (c = nextc(p)) {
              case ' ': case '\t': case '\f': case '\r':
              case '\13': /* '\v' */
                space_seen = 1;
                break;
              case '#':
                pushback(p, c);
                if (space_seen) {
                    dispatch_scan_event(p, tSP);
                    token_flush(p);
                }
                goto retry;
              case 'a':
                if (peek_word_at(p, "nd", 2, 0)) goto leading_logical;
                goto bol;
              case 'o':
                if (peek_word_at(p, "r", 1, 0)) goto leading_logical;
                goto bol;
              case '|':
                if (peek(p, '|')) goto leading_logical;
                goto bol;
              case '&':
                if (peek(p, '&')) {
                  leading_logical:
                    pushback(p, c);
                    dispatch_delayed_token(p, tIGNORED_NL);
                    cmd_state = FALSE;
                    goto retry;
                }
                /* fall through */
              case '.': {
                dispatch_delayed_token(p, tIGNORED_NL);
                if (peek(p, '.') == (c == '&')) {
                    pushback(p, c);
                    dispatch_scan_event(p, tSP);
                    goto retry;
                }
              }
              bol:
              default:
                p->ruby_sourceline--;
                p->lex.nextline = p->lex.lastline;
                set_lastline(p, prevline);
              case -1:		/* EOF no decrement*/
                if (c == -1 && space_seen) {
                    dispatch_scan_event(p, tSP);
                }
                lex_goto_eol(p);
                if (c != -1) {
                    token_flush(p);
                    RUBY_SET_YYLLOC(*p->yylloc);
                }
                goto normal_newline;
            }
        }
      normal_newline:
        p->command_start = TRUE;
        SET_LEX_STATE(EXPR_BEG);
        return '\n';

      case '*':
        if ((c = nextc(p)) == '*') {
            if ((c = nextc(p)) == '=') {
                set_yylval_id(idPow);
                SET_LEX_STATE(EXPR_BEG);
                return tOP_ASGN;
            }
            pushback(p, c);
            if (IS_SPCARG(c)) {
                rb_warning0("'**' interpreted as argument prefix");
                c = tDSTAR;
            }
            else if (IS_BEG()) {
                c = tDSTAR;
            }
            else {
                c = warn_balanced((enum ruby_method_ids)tPOW, "**", "argument prefix");
            }
        }
        else {
            if (c == '=') {
                set_yylval_id('*');
                SET_LEX_STATE(EXPR_BEG);
                return tOP_ASGN;
            }
            pushback(p, c);
            if (IS_SPCARG(c)) {
                rb_warning0("'*' interpreted as argument prefix");
                c = tSTAR;
            }
            else if (IS_BEG()) {
                c = tSTAR;
            }
            else {
                c = warn_balanced('*', "*", "argument prefix");
            }
        }
        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
        return c;

      case '!':
        c = nextc(p);
        if (IS_AFTER_OPERATOR()) {
            SET_LEX_STATE(EXPR_ARG);
            if (c == '@') {
                return '!';
            }
        }
        else {
            SET_LEX_STATE(EXPR_BEG);
        }
        if (c == '=') {
            return tNEQ;
        }
        if (c == '~') {
            return tNMATCH;
        }
        pushback(p, c);
        return '!';

      case '=':
        if (was_bol(p)) {
            /* skip embedded rd document */
            if (word_match_p(p, "begin", 5)) {
                int first_p = TRUE;

                lex_goto_eol(p);
                dispatch_scan_event(p, tEMBDOC_BEG);
                for (;;) {
                    lex_goto_eol(p);
                    if (!first_p) {
                        dispatch_scan_event(p, tEMBDOC);
                    }
                    first_p = FALSE;
                    c = nextc(p);
                    if (c == -1) {
                        compile_error(p, "embedded document meets end of file");
                        return END_OF_INPUT;
                    }
                    if (c == '=' && word_match_p(p, "end", 3)) {
                        break;
                    }
                    pushback(p, c);
                }
                lex_goto_eol(p);
                dispatch_scan_event(p, tEMBDOC_END);
                goto retry;
            }
        }

        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
        if ((c = nextc(p)) == '=') {
            if ((c = nextc(p)) == '=') {
                return tEQQ;
            }
            pushback(p, c);
            return tEQ;
        }
        if (c == '~') {
            return tMATCH;
        }
        else if (c == '>') {
            return tASSOC;
        }
        pushback(p, c);
        return '=';

      case '<':
        c = nextc(p);
        if (c == '<' &&
            !IS_lex_state(EXPR_DOT | EXPR_CLASS) &&
            !IS_END() &&
            (!IS_ARG() || IS_lex_state(EXPR_LABELED) || space_seen)) {
            enum  yytokentype token = heredoc_identifier(p);
            if (token) return token < 0 ? 0 : token;
        }
        if (IS_AFTER_OPERATOR()) {
            SET_LEX_STATE(EXPR_ARG);
        }
        else {
            if (IS_lex_state(EXPR_CLASS))
                p->command_start = TRUE;
            SET_LEX_STATE(EXPR_BEG);
        }
        if (c == '=') {
            if ((c = nextc(p)) == '>') {
                return tCMP;
            }
            pushback(p, c);
            return tLEQ;
        }
        if (c == '<') {
            if ((c = nextc(p)) == '=') {
                set_yylval_id(idLTLT);
                SET_LEX_STATE(EXPR_BEG);
                return tOP_ASGN;
            }
            pushback(p, c);
            return warn_balanced((enum ruby_method_ids)tLSHFT, "<<", "here document");
        }
        pushback(p, c);
        return '<';

      case '>':
        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
        if ((c = nextc(p)) == '=') {
            return tGEQ;
        }
        if (c == '>') {
            if ((c = nextc(p)) == '=') {
                set_yylval_id(idGTGT);
                SET_LEX_STATE(EXPR_BEG);
                return tOP_ASGN;
            }
            pushback(p, c);
            return tRSHFT;
        }
        pushback(p, c);
        return '>';

      case '"':
        label = (IS_LABEL_POSSIBLE() ? str_label : 0);
        p->lex.strterm = NEW_STRTERM(str_dquote | label, '"', 0);
        p->lex.ptok = p->lex.pcur-1;
        return tSTRING_BEG;

      case '`':
        if (IS_lex_state(EXPR_FNAME)) {
            SET_LEX_STATE(EXPR_ENDFN);
            return c;
        }
        if (IS_lex_state(EXPR_DOT)) {
            if (cmd_state)
                SET_LEX_STATE(EXPR_CMDARG);
            else
                SET_LEX_STATE(EXPR_ARG);
            return c;
        }
        p->lex.strterm = NEW_STRTERM(str_xquote, '`', 0);
        return tXSTRING_BEG;

      case '\'':
        label = (IS_LABEL_POSSIBLE() ? str_label : 0);
        p->lex.strterm = NEW_STRTERM(str_squote | label, '\'', 0);
        p->lex.ptok = p->lex.pcur-1;
        return tSTRING_BEG;

      case '?':
        return parse_qmark(p, space_seen);

      case '&':
        if ((c = nextc(p)) == '&') {
            SET_LEX_STATE(EXPR_BEG);
            if ((c = nextc(p)) == '=') {
                set_yylval_id(idANDOP);
                SET_LEX_STATE(EXPR_BEG);
                return tOP_ASGN;
            }
            pushback(p, c);
            return tANDOP;
        }
        else if (c == '=') {
            set_yylval_id('&');
            SET_LEX_STATE(EXPR_BEG);
            return tOP_ASGN;
        }
        else if (c == '.') {
            set_yylval_id(idANDDOT);
            SET_LEX_STATE(EXPR_DOT);
            return tANDDOT;
        }
        pushback(p, c);
        if (IS_SPCARG(c)) {
            if ((c != ':') ||
                (c = peekc_n(p, 1)) == -1 ||
                !(c == '\'' || c == '"' ||
                  is_identchar(p, (p->lex.pcur+1), p->lex.pend, p->enc))) {
                rb_warning0("'&' interpreted as argument prefix");
            }
            c = tAMPER;
        }
        else if (IS_BEG()) {
            c = tAMPER;
        }
        else {
            c = warn_balanced('&', "&", "argument prefix");
        }
        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
        return c;

      case '|':
        if ((c = nextc(p)) == '|') {
            SET_LEX_STATE(EXPR_BEG);
            if ((c = nextc(p)) == '=') {
                set_yylval_id(idOROP);
                SET_LEX_STATE(EXPR_BEG);
                return tOP_ASGN;
            }
            pushback(p, c);
            if (IS_lex_state_for(last_state, EXPR_BEG)) {
                c = '|';
                pushback(p, '|');
                return c;
            }
            return tOROP;
        }
        if (c == '=') {
            set_yylval_id('|');
            SET_LEX_STATE(EXPR_BEG);
            return tOP_ASGN;
        }
        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG|EXPR_LABEL);
        pushback(p, c);
        return '|';

      case '+':
        c = nextc(p);
        if (IS_AFTER_OPERATOR()) {
            SET_LEX_STATE(EXPR_ARG);
            if (c == '@') {
                return tUPLUS;
            }
            pushback(p, c);
            return '+';
        }
        if (c == '=') {
            set_yylval_id('+');
            SET_LEX_STATE(EXPR_BEG);
            return tOP_ASGN;
        }
        if (IS_BEG() || (IS_SPCARG(c) && arg_ambiguous(p, '+'))) {
            SET_LEX_STATE(EXPR_BEG);
            pushback(p, c);
            if (c != -1 && ISDIGIT(c)) {
                return parse_numeric(p, '+');
            }
            return tUPLUS;
        }
        SET_LEX_STATE(EXPR_BEG);
        pushback(p, c);
        return warn_balanced('+', "+", "unary operator");

      case '-':
        c = nextc(p);
        if (IS_AFTER_OPERATOR()) {
            SET_LEX_STATE(EXPR_ARG);
            if (c == '@') {
                return tUMINUS;
            }
            pushback(p, c);
            return '-';
        }
        if (c == '=') {
            set_yylval_id('-');
            SET_LEX_STATE(EXPR_BEG);
            return tOP_ASGN;
        }
        if (c == '>') {
            SET_LEX_STATE(EXPR_ENDFN);
            yylval.num = p->lex.lpar_beg;
            p->lex.lpar_beg = p->lex.paren_nest;
            return tLAMBDA;
        }
        if (IS_BEG() || (IS_SPCARG(c) && arg_ambiguous(p, '-'))) {
            SET_LEX_STATE(EXPR_BEG);
            pushback(p, c);
            if (c != -1 && ISDIGIT(c)) {
                return tUMINUS_NUM;
            }
            return tUMINUS;
        }
        SET_LEX_STATE(EXPR_BEG);
        pushback(p, c);
        return warn_balanced('-', "-", "unary operator");

      case '.': {
        int is_beg = IS_BEG();
        SET_LEX_STATE(EXPR_BEG);
        if ((c = nextc(p)) == '.') {
            if ((c = nextc(p)) == '.') {
                if (p->ctxt.in_argdef || IS_LABEL_POSSIBLE()) {
                    SET_LEX_STATE(EXPR_ENDARG);
                    return tBDOT3;
                }
                if (p->lex.paren_nest == 0 && looking_at_eol_p(p)) {
                    rb_warn0("... at EOL, should be parenthesized?");
                }
                return is_beg ? tBDOT3 : tDOT3;
            }
            pushback(p, c);
            return is_beg ? tBDOT2 : tDOT2;
        }
        pushback(p, c);
        if (c != -1 && ISDIGIT(c)) {
            char prev = p->lex.pcur-1 > p->lex.pbeg ? *(p->lex.pcur-2) : 0;
            parse_numeric(p, '.');
            if (ISDIGIT(prev)) {
                yyerror0("unexpected fraction part after numeric literal");
            }
            else {
                yyerror0("no .<digit> floating literal anymore; put 0 before dot");
            }
            SET_LEX_STATE(EXPR_END);
            p->lex.ptok = p->lex.pcur;
            goto retry;
        }
        set_yylval_id('.');
        SET_LEX_STATE(EXPR_DOT);
        return '.';
      }

      case '0': case '1': case '2': case '3': case '4':
      case '5': case '6': case '7': case '8': case '9':
        return parse_numeric(p, c);

      case ')':
        COND_POP();
        CMDARG_POP();
        SET_LEX_STATE(EXPR_ENDFN);
        p->lex.paren_nest--;
        return c;

      case ']':
        COND_POP();
        CMDARG_POP();
        SET_LEX_STATE(EXPR_END);
        p->lex.paren_nest--;
        return c;

      case '}':
        /* tSTRING_DEND does COND_POP and CMDARG_POP in the yacc's rule */
        if (!p->lex.brace_nest--) return tSTRING_DEND;
        COND_POP();
        CMDARG_POP();
        SET_LEX_STATE(EXPR_END);
        p->lex.paren_nest--;
        return c;

      case ':':
        c = nextc(p);
        if (c == ':') {
            if (IS_BEG() || IS_lex_state(EXPR_CLASS) || IS_SPCARG(-1)) {
                SET_LEX_STATE(EXPR_BEG);
                return tCOLON3;
            }
            set_yylval_id(idCOLON2);
            SET_LEX_STATE(EXPR_DOT);
            return tCOLON2;
        }
        if (IS_END() || ISSPACE(c) || c == '#') {
            pushback(p, c);
            c = warn_balanced(':', ":", "symbol literal");
            SET_LEX_STATE(EXPR_BEG);
            return c;
        }
        switch (c) {
          case '\'':
            p->lex.strterm = NEW_STRTERM(str_ssym, c, 0);
            break;
          case '"':
            p->lex.strterm = NEW_STRTERM(str_dsym, c, 0);
            break;
          default:
            pushback(p, c);
            break;
        }
        SET_LEX_STATE(EXPR_FNAME);
        return tSYMBEG;

      case '/':
        if (IS_BEG()) {
            p->lex.strterm = NEW_STRTERM(str_regexp, '/', 0);
            return tREGEXP_BEG;
        }
        if ((c = nextc(p)) == '=') {
            set_yylval_id('/');
            SET_LEX_STATE(EXPR_BEG);
            return tOP_ASGN;
        }
        pushback(p, c);
        if (IS_SPCARG(c)) {
            p->lex.strterm = NEW_STRTERM(str_regexp, '/', 0);
            return tREGEXP_BEG;
        }
        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
        return warn_balanced('/', "/", "regexp literal");

      case '^':
        if ((c = nextc(p)) == '=') {
            set_yylval_id('^');
            SET_LEX_STATE(EXPR_BEG);
            return tOP_ASGN;
        }
        SET_LEX_STATE(IS_AFTER_OPERATOR() ? EXPR_ARG : EXPR_BEG);
        pushback(p, c);
        return '^';

      case ';':
        SET_LEX_STATE(EXPR_BEG);
        p->command_start = TRUE;
        return ';';

      case ',':
        SET_LEX_STATE(EXPR_BEG|EXPR_LABEL);
        return ',';

      case '~':
        if (IS_AFTER_OPERATOR()) {
            if ((c = nextc(p)) != '@') {
                pushback(p, c);
            }
            SET_LEX_STATE(EXPR_ARG);
        }
        else {
            SET_LEX_STATE(EXPR_BEG);
        }
        return '~';

      case '(':
        if (IS_BEG()) {
            c = tLPAREN;
        }
        else if (!space_seen) {
            /* foo( ... ) => method call, no ambiguity */
        }
        else if (IS_ARG() || IS_lex_state_all(EXPR_END|EXPR_LABEL)) {
            c = tLPAREN_ARG;
        }
        else if (IS_lex_state(EXPR_ENDFN) && !lambda_beginning_p()) {
            rb_warning0("parentheses after method name is interpreted as "
                        "an argument list, not a decomposed argument");
        }
        p->lex.paren_nest++;
        COND_PUSH(0);
        CMDARG_PUSH(0);
        SET_LEX_STATE(EXPR_BEG|EXPR_LABEL);
        return c;

      case '[':
        p->lex.paren_nest++;
        if (IS_AFTER_OPERATOR()) {
            if ((c = nextc(p)) == ']') {
                p->lex.paren_nest--;
                SET_LEX_STATE(EXPR_ARG);
                if ((c = nextc(p)) == '=') {
                    return tASET;
                }
                pushback(p, c);
                return tAREF;
            }
            pushback(p, c);
            SET_LEX_STATE(EXPR_ARG|EXPR_LABEL);
            return '[';
        }
        else if (IS_BEG()) {
            c = tLBRACK;
        }
        else if (IS_ARG() && (space_seen || IS_lex_state(EXPR_LABELED))) {
            c = tLBRACK;
        }
        SET_LEX_STATE(EXPR_BEG|EXPR_LABEL);
        COND_PUSH(0);
        CMDARG_PUSH(0);
        return c;

      case '{':
        ++p->lex.brace_nest;
        if (lambda_beginning_p())
            c = tLAMBEG;
        else if (IS_lex_state(EXPR_LABELED))
            c = tLBRACE;      /* hash */
        else if (IS_lex_state(EXPR_ARG_ANY | EXPR_END | EXPR_ENDFN))
            c = '{';          /* block (primary) */
        else if (IS_lex_state(EXPR_ENDARG))
            c = tLBRACE_ARG;  /* block (expr) */
        else
            c = tLBRACE;      /* hash */
        if (c != tLBRACE) {
            p->command_start = TRUE;
            SET_LEX_STATE(EXPR_BEG);
        }
        else {
            SET_LEX_STATE(EXPR_BEG|EXPR_LABEL);
        }
        ++p->lex.paren_nest;  /* after lambda_beginning_p() */
        COND_PUSH(0);
        CMDARG_PUSH(0);
        return c;

      case '\\':
        c = nextc(p);
        if (c == '\n') {
            space_seen = 1;
            dispatch_scan_event(p, tSP);
            goto retry; /* skip \\n */
        }
        if (c == ' ') return tSP;
        if (ISSPACE(c)) return c;
        pushback(p, c);
        return '\\';

      case '%':
        return parse_percent(p, space_seen, last_state);

      case '$':
        return parse_gvar(p, last_state);

      case '@':
        return parse_atmark(p, last_state);

      case '_':
        if (was_bol(p) && whole_match_p(p, "__END__", 7, 0)) {
            p->ruby__end__seen = 1;
            p->eofp = 1;
            return END_OF_INPUT;
        }
        newtok(p);
        break;

      default:
        if (!parser_is_identchar(p)) {
            compile_error(p, "Invalid char '\\x%02X' in expression", c);
            token_flush(p);
            goto retry;
        }

        newtok(p);
        break;
    }

    return parse_ident(p, c, cmd_state);
}

static enum yytokentype
yylex(YYSTYPE *lval, YYLTYPE *yylloc, struct parser_params *p)
{
    enum yytokentype t;

    p->lval = lval;
    lval->node = 0;
    p->yylloc = yylloc;

    t = parser_yylex(p);

    if (has_delayed_token(p))
        dispatch_delayed_token(p, t);
    else if (t != END_OF_INPUT)
        dispatch_scan_event(p, t);

    return t;
}

#define LVAR_USED ((ID)1 << (sizeof(ID) * CHAR_BIT - 1))

static NODE*
node_new_internal(struct parser_params *p, enum node_type type, size_t size, size_t alignment)
{
    YSTUB("node_new_internal");
    return NULL;
}

static NODE *
nd_set_loc(NODE *nd, const YYLTYPE *loc)
{
    return nd;
}

static NODE*
node_newnode(struct parser_params *p, enum node_type type, size_t size, size_t alignment, const rb_code_location_t *loc)
{
    YSTUB("node_newnode");
    return NULL;
}

#define NODE_NEWNODE(node_type, type, loc) (type *)(node_newnode(p, node_type, sizeof(type), RUBY_ALIGNOF(type), loc))

/*
 * PORTED CONSTRUCTORS. From here down, functions are either stubs (YSTUB) or
 * real prism node construction; they convert from CRuby's calling conventions
 * at this boundary so the grammar actions above stay upstream-shaped.
 */

/*
 * Take ownership of a lexer-built string's bytes as a node-held pm_string_t:
 * copied into the arena the node lives in, which is the convention prism's
 * own string nodes follow (nodes never hold heap-owned strings). The ystring
 * is consumed.
 */
static pm_string_t
pm_ystr_take(struct parser_params *p, rb_parser_string_t *str)
{
    pm_string_t result;

    if (str == NULL || str->len == 0) {
        result = PM_STRING_EMPTY;
    }
    else {
        uint8_t *bytes = (uint8_t *) pm_arena_alloc(p->pm->arena, (size_t) str->len, 1);
        memcpy(bytes, str->ptr, (size_t) str->len);
        pm_string_constant_init(&result, (const char *) bytes, (size_t) str->len);
    }

    pm_ystring_free(str);
    return result;
}

/*
 * Attach the quote locations to a string-family literal once the closing
 * token is known; the constructor only sees the content. Called from the
 * string1 action, which is where CRuby re-locates the node too.
 */
static NODE *
string_literal_quotes(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc)
{
    if (node == NULL) {
        /* Empty contents: the node carries a zero-width content location
         * between the quotes, as the hand-written parser produces. */
        pm_location_t content_loc = { opening->end, closing->beg - opening->end };
        node = (NODE *) pm_string_node_new(
            p->pm->arena, ++p->pm->node_id, 0, content_loc,
            (pm_location_t) { 0 }, content_loc, (pm_location_t) { 0 },
            PM_STRING_EMPTY);
    }

    if (PM_NODE_TYPE_P(node, PM_STRING_NODE)) {
        pm_string_node_t *string = (pm_string_node_t *) node;
        string->opening_loc = pm_yloc(opening);
        string->closing_loc = pm_yloc(closing);
        /* The lexer hands content over a line at a time, so the node's own
         * content location can cover just the last chunk; the full span is
         * everything between the quotes. */
        string->content_loc = (pm_location_t) { opening->end, closing->beg - opening->end };
        string->base.location = pm_yloc(loc);
    }
    else if (PM_NODE_TYPE_P(node, PM_EMBEDDED_STATEMENTS_NODE) || PM_NODE_TYPE_P(node, PM_EMBEDDED_VARIABLE_NODE)) {
        /* A string that is one interpolation and nothing else. */
        node = pm_yistr(p, node);
        pm_interpolated_string_node_t *istr = (pm_interpolated_string_node_t *) node;
        istr->opening_loc = pm_yloc(opening);
        istr->closing_loc = pm_yloc(closing);
        istr->base.location = pm_yloc(loc);
    }
    else if (PM_NODE_TYPE_P(node, PM_INTERPOLATED_STRING_NODE)) {
        pm_interpolated_string_node_t *istr = (pm_interpolated_string_node_t *) node;
        istr->opening_loc = pm_yloc(opening);
        istr->closing_loc = pm_yloc(closing);
        istr->base.location = pm_yloc(loc);
    }
    else {
        YSTUB("string_literal_quotes");
    }

    return node;
}

/* The constant pool id for an ID's name, in the fork's usual pools. Static
 * IDs (id.h) never went through pm_yid_intern, so their spellings are
 * supplied here as node construction comes to need them. */
static pm_constant_id_t
pm_yid2const(struct parser_params *p, ID id)
{
    const char *known = NULL;
    switch (id) {
      case idCall: known = "call"; break;
      default: break;
    }

    if (known != NULL) {
        return pm_constant_pool_insert_constant(&p->pm->metadata_arena, &p->pm->constant_pool, (const uint8_t *) known, strlen(known));
    }

    return pm_yid_to_constant(&p->pm->metadata_arena, &p->pm->constant_pool, id);
}
#define YID2CONST(id) pm_yid2const(p, (id))

/*
 * The depth of a block-local variable: how many enclosing block scopes up its
 * declaration lives, which is what prism's read/write nodes carry and CRuby's
 * nodes recompute at compile time.
 */
static uint32_t
pm_ydvar_depth(struct parser_params *p, ID id)
{
    uint32_t depth = 0;
    struct vtable *args = p->lvtbl->args;
    struct vtable *vars = p->lvtbl->vars;

    while (vars != NULL && !DVARS_TERMINAL_P(vars)) {
        if (vtable_included(vars, id)) return depth;
        if (args != NULL && !DVARS_TERMINAL_P(args) && vtable_included(args, id)) return depth;
        vars = vars->prev;
        if (args != NULL) args = args->prev;
        depth++;
    }

    return 0;
}

/* A node's own span as a YYLTYPE, for the CRuby idiom of locating a new node
 * at an existing one (&node->nd_loc upstream). */
static inline YYLTYPE
pm_yloc_of(const NODE *node)
{
    return (YYLTYPE) { node->location.start, node->location.start + node->location.length };
}

/*
 * Argument lists. CRuby carries call arguments as the same NODE_LIST it uses
 * for array literals; prism separates ArgumentsNode from ArrayNode. The fork
 * builds lists as bare ArrayNodes (no brackets) and converts at the call
 * constructors, which are the points that know the list is arguments.
 */
static pm_arguments_node_t *
pm_yargs_from_list(struct parser_params *p, NODE *list)
{
    if (list == NULL || NODE_EMPTY_ARGS_P(list)) return NULL;

    pm_node_list_t arguments = { 0 };
    pm_location_t location;
    if (PM_NODE_TYPE_P(list, PM_ARRAY_NODE)) {
        arguments = ((pm_array_node_t *) list)->elements;
        location = list->location;
    }
    else {
        /* a single expression (ret_args unwraps one-element lists) */
        pm_node_list_append(p->pm->arena, &arguments, list);
        location = list->location;
    }

    pm_node_flags_t flags = 0;
    size_t splats = 0;
    for (size_t i = 0; i < arguments.size; i++) {
        pm_node_t *argument = arguments.nodes[i];
        if (argument == NULL) continue;
        switch (PM_NODE_TYPE(argument)) {
          case PM_SPLAT_NODE:
            splats++;
            break;
          case PM_KEYWORD_HASH_NODE: {
            flags |= PM_ARGUMENTS_NODE_FLAGS_CONTAINS_KEYWORDS;
            pm_node_list_t pairs = ((pm_keyword_hash_node_t *) argument)->elements;
            for (size_t j = 0; j < pairs.size; j++) {
                if (PM_NODE_TYPE_P(pairs.nodes[j], PM_ASSOC_SPLAT_NODE)) {
                    flags |= PM_ARGUMENTS_NODE_FLAGS_CONTAINS_KEYWORD_SPLAT;
                }
            }
            break;
          }
          default:
            break;
        }
    }
    if (splats > 0) flags |= PM_ARGUMENTS_NODE_FLAGS_CONTAINS_SPLAT;
    if (splats > 1) flags |= PM_ARGUMENTS_NODE_FLAGS_CONTAINS_MULTIPLE_SPLATS;

    return pm_arguments_node_new(p->pm->arena, ++p->pm->node_id, flags, location, arguments);
}

/* Attach the pending &block argument, if any, to the given call. */
static void
pm_yblock_pass_take(struct parser_params *p, pm_call_node_t *call)
{
    if (p->yblock_pass == NULL) return;
    call->block = p->yblock_pass;
    p->yblock_pass = NULL;
}

/* Record the parentheses of a paren_args reduction for the call about to
 * consume them. */
static void
pm_yparens_set(struct parser_params *p, const YYLTYPE *opening, const YYLTYPE *closing)
{
    p->yparens.opening = *opening;
    p->yparens.closing = *closing;
    p->yparens.set = 1;
}

/* Attach the pending parentheses, if any, to the given call. */
static void
pm_yparens_take(struct parser_params *p, pm_call_node_t *call)
{
    if (!p->yparens.set) return;
    call->opening_loc = pm_yloc(&p->yparens.opening);
    call->closing_loc = pm_yloc(&p->yparens.closing);
    p->yparens.set = 0;
}

/*
 * The location of the call operator (`.`, `&.`, `::`) between a receiver and
 * its message. The grammar does not pass it down (CRuby's nodes never store
 * it), but it is recoverable: it is the only token between the two, so a
 * forward scan that skips whitespace and comments finds it exactly.
 */
static pm_location_t
pm_ycall_operator_scan(struct parser_params *p, uint32_t from, uint32_t upto)
{
    const uint8_t *source = p->pm->start;
    uint32_t scan = from;

    while (scan < upto) {
        uint8_t c = source[scan];
        if (c == '#') {
            while (scan < upto && source[scan] != '\n') scan++;
        }
        else if (c == '.' && scan + 1 < upto && source[scan + 1] == '.') {
            /* not reachable for call operators; guards against ranges */
            scan += 2;
        }
        else if (c == '.') {
            return (pm_location_t) { scan, 1 };
        }
        else if (c == '&' && scan + 1 < upto && source[scan + 1] == '.') {
            return (pm_location_t) { scan, 2 };
        }
        else if (c == ':' && scan + 1 < upto && source[scan + 1] == ':') {
            return (pm_location_t) { scan, 2 };
        }
        else {
            scan++;
        }
    }

    return (pm_location_t) { 0 };
}

/*
 * Attach arguments (and any pending parentheses) to a parenless-constructed
 * call: the fcall and command forms build the CallNode from the method name
 * alone and the arguments arrive in a later part of the rule.
 */
static NODE *
pm_yfcall_args(struct parser_params *p, NODE *node, NODE *args, const YYLTYPE *loc)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_CALL_NODE)) {
        YSTUB("pm_yfcall_args");
        return node;
    }

    pm_call_node_t *call = (pm_call_node_t *) node;
    if (NODE_EMPTY_ARGS_P(args)) args = 0;
    call->arguments = pm_yargs_from_list(p, args);
    pm_yparens_take(p, call);
    pm_yblock_pass_take(p, call);
    call->base.location = pm_yloc(loc);
    return node;
}

/* The ID's spelling out of the constant pool (or the operator name table),
 * as an owned ystring. */
static rb_parser_string_t *
pm_yid2str(struct parser_params *p, ID id)
{
    const char *op = pm_yid_op_name(id);
    if (op != NULL) return pm_ystring_new(op, (long) strlen(op), p->enc);

    pm_constant_id_t constant_id = pm_yid2const(p, id);
    if (constant_id == PM_CONSTANT_ID_UNSET) return NULL;

    pm_constant_t *constant = pm_constant_pool_id_to_constant(&p->pm->constant_pool, constant_id);
    return pm_ystring_new((const char *) constant->start, (long) constant->length, p->enc);
}

/* A class/module/singleton-class body: rescue/ensure clauses hang directly
 * off the definition, spanning it entirely with the end keyword stamped. */
static pm_node_t *pm_yclass_body(struct parser_params *p, NODE *body, const YYLTYPE *loc, const YYLTYPE *end_keyword_loc);

/* Wrap a body (or NULL) for a node that wants an optional StatementsNode:
 * unlike pm_ystatements_ensure, an absent body stays absent. */
static pm_statements_node_t *
pm_ystatements_opt(struct parser_params *p, NODE *body)
{
    return body == NULL ? NULL : pm_ystatements_ensure(p, body);
}

/* The current scope's locals as prism's constant list, consuming the
 * local_tbl the scope machinery built. */
static pm_constant_id_list_t
pm_ylocals(struct parser_params *p)
{
    pm_constant_id_list_t locals = { 0 };
    rb_ast_id_table_t *tbl = local_tbl(p);

    if (tbl != NULL) {
        pm_constant_id_list_init_capacity(&p->pm->metadata_arena, &locals, (size_t) tbl->size);
        for (int i = 0; i < tbl->size; i++) {
            /* anonymous forwarding markers (*, **, &, ...) are not locals */
            ID id = tbl->ids[i];
            if (id == idFWD_REST || id == idFWD_KWREST || id == idFWD_BLOCK || id == idFWD_ALL) continue;
            pm_constant_id_list_append(&p->pm->metadata_arena, &locals, pm_yid2const(p, id));
        }
        xfree(tbl);
    }

    return locals;
}

/* Fold the static-literal / contains-splat flags onto a bracketless array
 * (an mrhs list or an svalue splat) the way the hand parser marks values. */
static NODE *
pm_yarray_finalize(struct parser_params *p, NODE *node)
{
    (void) p;
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_ARRAY_NODE)) return node;

    pm_array_node_t *array = (pm_array_node_t *) node;
    if (array->opening_loc.length > 0) return node; /* a real literal, already folded */

    bool is_static = array->elements.size > 0;
    for (size_t i = 0; i < array->elements.size; i++) {
        pm_node_t *element = array->elements.nodes[i];
        if (PM_NODE_TYPE_P(element, PM_SPLAT_NODE)) {
            array->base.flags |= PM_ARRAY_NODE_FLAGS_CONTAINS_SPLAT;
            is_static = false;
        }
        else if (!PM_NODE_FLAG_P(element, PM_NODE_FLAG_STATIC_LITERAL) ||
                 PM_NODE_TYPE_P(element, PM_ARRAY_NODE) || PM_NODE_TYPE_P(element, PM_HASH_NODE)) {
            is_static = false;
        }
    }
    if (is_static) array->base.flags |= PM_NODE_FLAG_STATIC_LITERAL;
    return node;
}

/* Stamp the parentheses of an (a, b) group onto its target node. */
static void
pm_ymulti_parens(struct parser_params *p, NODE *node, const YYLTYPE *lparen, const YYLTYPE *rparen)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_MULTI_TARGET_NODE)) return;
    pm_multi_target_node_t *target = (pm_multi_target_node_t *) node;
    target->lparen_loc = pm_yloc(lparen);
    target->rparen_loc = pm_yloc(rparen);
    target->base.location = (pm_location_t) { lparen->beg, rparen->end - lparen->beg };
}

/* A write node built by assignable() re-expressed as prism's target node,
 * for the positions that bind without assigning (rescue => e, for x in ...). */
static NODE *
pm_ytarget(struct parser_params *p, NODE *node)
{
    if (node == NULL) return NULL;

    pm_location_t loc = node->location;
    switch (PM_NODE_TYPE(node)) {
      case PM_LOCAL_VARIABLE_WRITE_NODE: {
        pm_local_variable_write_node_t *write = (pm_local_variable_write_node_t *) node;
        return (NODE *) pm_local_variable_target_node_new(p->pm->arena, ++p->pm->node_id, 0, loc, write->name, write->depth);
      }
      case PM_INSTANCE_VARIABLE_WRITE_NODE:
        return (NODE *) pm_instance_variable_target_node_new(p->pm->arena, ++p->pm->node_id, 0, loc, ((pm_instance_variable_write_node_t *) node)->name);
      case PM_GLOBAL_VARIABLE_WRITE_NODE:
        return (NODE *) pm_global_variable_target_node_new(p->pm->arena, ++p->pm->node_id, 0, loc, ((pm_global_variable_write_node_t *) node)->name);
      case PM_CLASS_VARIABLE_WRITE_NODE:
        return (NODE *) pm_class_variable_target_node_new(p->pm->arena, ++p->pm->node_id, 0, loc, ((pm_class_variable_write_node_t *) node)->name);
      case PM_CONSTANT_WRITE_NODE:
        return (NODE *) pm_constant_target_node_new(p->pm->arena, ++p->pm->node_id, 0, loc, ((pm_constant_write_node_t *) node)->name);
      case PM_CONSTANT_PATH_WRITE_NODE: {
        pm_constant_path_node_t *path = ((pm_constant_path_write_node_t *) node)->target;
        return (NODE *) pm_constant_path_target_node_new(
            p->pm->arena, ++p->pm->node_id, 0, path->base.location,
            path->parent, path->name, path->delimiter_loc, path->name_loc);
      }
      case PM_CALL_NODE: {
        pm_call_node_t *call = (pm_call_node_t *) node;
        if (!PM_NODE_FLAG_P(node, PM_CALL_NODE_FLAGS_ATTRIBUTE_WRITE)) break;
        if (call->opening_loc.length > 0) {
            /* an index write: a[i] */
            return (NODE *) pm_index_target_node_new(
                p->pm->arena, ++p->pm->node_id, PM_CALL_NODE_FLAGS_ATTRIBUTE_WRITE, loc,
                call->receiver, call->opening_loc, call->arguments, call->closing_loc,
                (pm_block_argument_node_t *) call->block);
        }
        return (NODE *) pm_call_target_node_new(
            p->pm->arena, ++p->pm->node_id, 0, loc,
            call->receiver, call->call_operator_loc, call->name, call->message_loc);
      }
      case PM_MULTI_TARGET_NODE:
        /* a nested (a, b) group is already a target */
        return node;
      default:
        break;
    }
    YSTUB("pm_ytarget");
    return node;
}

/* An ensure clause; the end keyword arrives when the enclosing block closes. */
static NODE *
pm_yensure(struct parser_params *p, NODE *body, const YYLTYPE *ensure_loc, const YYLTYPE *loc)
{
    return (NODE *) pm_ensure_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(ensure_loc), pm_ystatements_opt(p, body), (pm_location_t) { 0 });
}

/* Complete a rescue clause with the locations only its reduction has: the
 * keyword, a then keyword if one was written, and the => scanned between
 * the clause head and the reference. */
static NODE *
pm_yrescue_finish(struct parser_params *p, NODE *node, const YYLTYPE *keyword_loc, const YYLTYPE *then_loc)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_RESCUE_NODE)) {
        YSTUB("pm_yrescue_finish");
        return node;
    }

    pm_rescue_node_t *rescue = (pm_rescue_node_t *) node;
    rescue->keyword_loc = pm_yloc(keyword_loc);

    if (rescue->reference != NULL) {
        uint32_t from = rescue->exceptions.size > 0
            ? rescue->exceptions.nodes[rescue->exceptions.size - 1]->location.start + rescue->exceptions.nodes[rescue->exceptions.size - 1]->location.length
            : rescue->keyword_loc.start + rescue->keyword_loc.length;
        const uint8_t *source = p->pm->start;
        uint32_t scan = from;
        while (scan + 1 < rescue->reference->location.start) {
            if (source[scan] == '=' && source[scan + 1] == '>') {
                rescue->operator_loc = (pm_location_t) { scan, 2 };
                break;
            }
            if (source[scan] == '#') { while (scan < rescue->reference->location.start && source[scan] != '\n') scan++; }
            else scan++;
        }
    }

    /* `then` was written iff the token really spells it. */
    if (then_loc->end - then_loc->beg == 4 && memcmp(p->pm->start + then_loc->beg, "then", 4) == 0) {
        rescue->then_keyword_loc = pm_yloc(then_loc);
    }

    /* The span runs to the last clause's own body, not to the term that
     * closed the reduction. */
    uint32_t end = rescue->keyword_loc.start + rescue->keyword_loc.length;
    if (rescue->subsequent != NULL) {
        end = rescue->subsequent->base.location.start + rescue->subsequent->base.location.length;
    }
    else if (rescue->statements != NULL) {
        end = rescue->statements->base.location.start + rescue->statements->base.location.length;
    }
    else if (rescue->reference != NULL) {
        end = rescue->reference->location.start + rescue->reference->location.length;
    }
    else if (rescue->exceptions.size > 0) {
        pm_node_t *last = rescue->exceptions.nodes[rescue->exceptions.size - 1];
        end = last->location.start + last->location.length;
    }
    rescue->base.location = (pm_location_t) { rescue->keyword_loc.start, end - rescue->keyword_loc.start };

    return node;
}

/* Stamp the closing `end` through a begin block: the block itself, and the
 * else/ensure clauses whose spans wait for it. */
static void
pm_ybegin_stamp_end(NODE *node, pm_location_t end_keyword)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_BEGIN_NODE)) return;
    pm_begin_node_t *begin = (pm_begin_node_t *) node;
    begin->end_keyword_loc = end_keyword;

    pm_location_t next_keyword = end_keyword;
    if (begin->ensure_clause != NULL) {
        pm_ensure_node_t *ensure = begin->ensure_clause;
        ensure->end_keyword_loc = end_keyword;
        uint32_t end = end_keyword.start + end_keyword.length;
        ensure->base.location.length = end - ensure->base.location.start;
        next_keyword = ensure->ensure_keyword_loc;
    }
    if (begin->else_clause != NULL) {
        pm_else_node_t *else_clause = begin->else_clause;
        else_clause->end_keyword_loc = next_keyword;
        uint32_t end = next_keyword.start + next_keyword.length;
        else_clause->base.location.length = end - else_clause->base.location.start;
    }
}

/* A string part entering an interpolation freezes: fragments of an
 * interpolated string are deduplicated literals like hash keys. */
static NODE *
pm_yistr_part(NODE *part)
{
    if (part != NULL && PM_NODE_TYPE_P(part, PM_STRING_NODE)) {
        part->flags |= PM_STRING_FLAGS_FROZEN | PM_NODE_FLAG_STATIC_LITERAL;
    }
    return part;
}

/* Wrap the first part of an interpolation into its carrier. */
static NODE *
pm_yistr(struct parser_params *p, NODE *part)
{
    pm_node_list_t parts = { 0 };
    pm_location_t location = part != NULL ? part->location : (pm_location_t) { 0 };
    if (part != NULL) pm_node_list_append(p->pm->arena, &parts, pm_yistr_part(part));
    return (NODE *) pm_interpolated_string_node_new(
        p->pm->arena, ++p->pm->node_id, 0, location,
        (pm_location_t) { 0 }, parts, (pm_location_t) { 0 });
}

static pm_node_t *
pm_yclass_body(struct parser_params *p, NODE *body, const YYLTYPE *loc, const YYLTYPE *end_keyword_loc)
{
    if (body != NULL && PM_NODE_TYPE_P(body, PM_BEGIN_NODE)) {
        pm_ybegin_stamp_end(body, pm_yloc(end_keyword_loc));
        body->location = pm_yloc(loc);
        return body;
    }
    return (pm_node_t *) pm_ystatements_opt(p, body);
}

/* The |params| of a block, or a lambda's -> (params). A NULL opening means
 * the undelimited lambda form ->a { }, whose span is the parameters' own. */
static NODE *
pm_yblock_params(struct parser_params *p, NODE *params, NODE *block_locals, const YYLTYPE *opening, const YYLTYPE *closing)
{
    (void) block_locals; /* PORTME: `; x` block-local declarations */

    pm_parameters_node_t *parameters =
        (params != NULL && PM_NODE_TYPE_P(params, PM_PARAMETERS_NODE)) ? (pm_parameters_node_t *) params : NULL;

    pm_location_t location;
    pm_location_t opening_loc = { 0 };
    pm_location_t closing_loc = { 0 };
    if (opening != NULL) {
        location = (pm_location_t) { opening->beg, closing->end - opening->beg };
        opening_loc = pm_yloc(opening);
        closing_loc = pm_yloc(closing);
    }
    else {
        if (parameters == NULL) return params;
        location = parameters->base.location;
    }

    return (NODE *) pm_block_parameters_node_new(
        p->pm->arena, ++p->pm->node_id, 0, location,
        parameters, (pm_node_list_t) { 0 }, opening_loc, closing_loc);
}

/* A modifier rescue: expr rescue fallback. */
static NODE *
pm_yrescue_modifier(struct parser_params *p, NODE *expr, NODE *fallback, const YYLTYPE *keyword_loc, const YYLTYPE *loc)
{
    return (NODE *) pm_rescue_modifier_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        expr, pm_yloc(keyword_loc), fallback);
}

/* A hash pair. String keys freeze (hash keys are deduplicated), and the pair
 * is a static literal when both halves are. */
static NODE *
pm_yassoc(struct parser_params *p, NODE *key, NODE *value, const YYLTYPE *operator_loc, const YYLTYPE *loc)
{
    if (key != NULL && PM_NODE_TYPE_P(key, PM_STRING_NODE)) {
        /* Hash keys deduplicate, so a string key is frozen -- and a frozen
         * string is a static literal. */
        key->flags |= PM_STRING_FLAGS_FROZEN | PM_NODE_FLAG_STATIC_LITERAL;
    }

    pm_node_flags_t flags = 0;
    if (key != NULL && value != NULL &&
        PM_NODE_FLAG_P(key, PM_NODE_FLAG_STATIC_LITERAL) &&
        PM_NODE_FLAG_P(value, PM_NODE_FLAG_STATIC_LITERAL) &&
        !PM_NODE_TYPE_P(value, PM_ARRAY_NODE) && !PM_NODE_TYPE_P(value, PM_HASH_NODE)) {
        flags = PM_NODE_FLAG_STATIC_LITERAL;
    }

    return (NODE *) pm_assoc_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc), key, value,
        operator_loc != NULL ? pm_yloc(operator_loc) : (pm_location_t) { 0 });
}

/* A label key (`a:`): a symbol whose colon is the closing. */
static NODE *
pm_ylabel_symbol(struct parser_params *p, ID label, const YYLTYPE *loc)
{
    pm_location_t location = pm_yloc(loc);
    pm_location_t value_loc = { location.start, location.length - 1 };
    pm_location_t closing_loc = { location.start + location.length - 1, 1 };

    rb_parser_string_t *str = pm_yid2str(p, label);
    pm_node_flags_t flags = PM_NODE_FLAG_STATIC_LITERAL;
    if (str == NULL || pm_ystring_coderange(str) == PM_YSTRING_CODERANGE_7BIT) {
        flags |= PM_SYMBOL_FLAGS_FORCED_US_ASCII_ENCODING;
    }

    return (NODE *) pm_symbol_node_new(
        p->pm->arena, ++p->pm->node_id, flags, location,
        (pm_location_t) { 0 }, value_loc, closing_loc,
        str == NULL ? PM_STRING_EMPTY : pm_ystr_take(p, str));
}

/* A **value pair in a hash or argument list. */
static NODE *
pm_yassoc_splat(struct parser_params *p, NODE *value, const YYLTYPE *operator_loc, const YYLTYPE *loc)
{
    return (NODE *) pm_assoc_splat_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), value, pm_yloc(operator_loc));
}

/* Attach the braces to a hash literal, with the array-style static fold. */
static NODE *
pm_yhash_braces(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_KEYWORD_HASH_NODE)) {
        YSTUB("pm_yhash_braces");
        return node;
    }

    /* the braced literal is a HashNode; new_hash built the keyword shape */
    pm_node_list_t elements = ((pm_keyword_hash_node_t *) node)->elements;
    pm_hash_node_t *hash = pm_hash_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(opening), elements, pm_yloc(closing));

    bool is_static = true;
    for (size_t i = 0; i < hash->elements.size; i++) {
        if (!PM_NODE_FLAG_P(hash->elements.nodes[i], PM_NODE_FLAG_STATIC_LITERAL)) {
            is_static = false;
            break;
        }
    }
    if (is_static) hash->base.flags |= PM_NODE_FLAG_STATIC_LITERAL;

    return (NODE *) hash;
}

/* Build a marker parameter (*rest, **kwrest, &block) at its reduction and
 * park it for new_args/new_args_tail; the grammar's own value stays the ID. */
static void
pm_ymarker_param(struct parser_params *p, NODE **slot, int kind, ID name, const YYLTYPE *mark_loc, const YYLTYPE *name_loc)
{
    pm_location_t mark = pm_yloc(mark_loc);
    pm_location_t name_location = { 0 };
    pm_location_t location = mark;
    pm_constant_id_t name_id = 0;

    if (name_loc != NULL) {
        name_location = pm_yloc(name_loc);
        location.length = (name_location.start + name_location.length) - location.start;
        name_id = pm_yid2const(p, name);
    }

    switch (kind) {
      case 0:
        *slot = (NODE *) pm_rest_parameter_node_new(p->pm->arena, ++p->pm->node_id, 0, location, name_id, name_location, mark);
        break;
      case 1:
        *slot = (NODE *) pm_keyword_rest_parameter_node_new(p->pm->arena, ++p->pm->node_id, 0, location, name_id, name_location, mark);
        break;
      default:
        *slot = (NODE *) pm_block_parameter_node_new(p->pm->arena, ++p->pm->node_id, 0, location, name_id, name_location, mark);
        break;
    }
}

/* A keyword parameter, required or optional by whether a default follows. */
static NODE *
pm_ykw_param(struct parser_params *p, ID label, NODE *value, const YYLTYPE *label_loc, const YYLTYPE *loc)
{
    /* the label token includes its colon; the name does not */
    pm_location_t name_location = pm_yloc(label_loc);
    pm_constant_id_t name = pm_yid2const(p, label);

    NODE *param;
    if (value == NULL || NODE_REQUIRED_KEYWORD_P(value)) {
        param = (NODE *) pm_required_keyword_parameter_node_new(
            p->pm->arena, ++p->pm->node_id, 0, name_location, name, name_location);
    }
    else {
        param = (NODE *) pm_optional_keyword_parameter_node_new(
            p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), name, name_location, value);
    }

    pm_node_list_t elements = { 0 };
    pm_node_list_append(p->pm->arena, &elements, param);
    return (NODE *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, param->location, elements,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

/* The `then` nonterminal spans a terminator, the keyword, or both; prism
 * records only the keyword itself, or nothing when it was elided. */
static pm_location_t
pm_ythen_loc(struct parser_params *p, const YYLTYPE *loc)
{
    uint32_t beg = loc->beg;
    uint32_t end = loc->end;
    if (end - beg >= 4 && memcmp(p->pm->start + end - 4, "then", 4) == 0) {
        return (pm_location_t) { end - 4, 4 };
    }
    /* the ternary operator records its ? here */
    if (end - beg == 1 && p->pm->start[beg] == '?') {
        return (pm_location_t) { beg, 1 };
    }
    return (pm_location_t) { 0 };
}

/* Assemble a case: split the clause carrier into when-conditions and the
 * trailing else, and stamp the end keyword through the else. */
static NODE *
pm_ycase(struct parser_params *p, NODE *predicate, NODE *body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    pm_node_list_t conditions = { 0 };
    pm_else_node_t *else_clause = NULL;
    pm_location_t end_keyword = pm_yloc(end_keyword_loc);

    if (body != NULL && PM_NODE_TYPE_P(body, PM_ARRAY_NODE)) {
        pm_array_node_t *carrier = (pm_array_node_t *) body;
        for (size_t i = 0; i < carrier->elements.size; i++) {
            pm_node_t *clause = carrier->elements.nodes[i];
            if (PM_NODE_TYPE_P(clause, PM_ELSE_NODE)) {
                else_clause = (pm_else_node_t *) clause;
                else_clause->end_keyword_loc = end_keyword;
                uint32_t end = end_keyword.start + end_keyword.length;
                else_clause->base.location.length = end - else_clause->base.location.start;
            }
            else {
                pm_node_list_append(p->pm->arena, &conditions, clause);
            }
        }
    }
    else if (body != NULL) {
        YSTUB("pm_ycase");
    }

    return (NODE *) pm_case_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        predicate, conditions, else_clause, pm_yloc(case_keyword_loc), end_keyword);
}

/* The defining name of a class/module: the last segment of its path. */
static pm_constant_id_t
pm_yconstant_path_name(NODE *cpath)
{
    if (cpath == NULL) return 0;
    if (PM_NODE_TYPE_P(cpath, PM_CONSTANT_READ_NODE)) return ((pm_constant_read_node_t *) cpath)->name;
    if (PM_NODE_TYPE_P(cpath, PM_CONSTANT_PATH_NODE)) return ((pm_constant_path_node_t *) cpath)->name;
    return 0;
}

/* Fill in a method definition's keyword and name locations, which only the
 * defn_head/defs_head actions have at hand. */
static void
pm_ydef_head(struct parser_params *p, NODE *node, const YYLTYPE *def_loc, const YYLTYPE *operator_loc, const YYLTYPE *name_loc)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_DEF_NODE)) return;
    pm_def_node_t *def = (pm_def_node_t *) node;
    def->def_keyword_loc = pm_yloc(def_loc);
    if (operator_loc != NULL) def->operator_loc = pm_yloc(operator_loc);
    def->name_loc = pm_yloc(name_loc);
}

/* Complete a method definition as its body closes: the span, the end keyword,
 * the body, the scope's locals, and any parameter parentheses. */
static NODE *
pm_ydef_finish(struct parser_params *p, NODE *node, NODE *args, NODE *body, const YYLTYPE *loc, const YYLTYPE *end_loc)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_DEF_NODE)) {
        YSTUB("pm_ydef_finish");
        return node;
    }

    pm_def_node_t *def = (pm_def_node_t *) node;
    def->base.location = pm_yloc(loc);
    def->end_keyword_loc = pm_yloc(end_loc);
    if (body != NULL && PM_NODE_TYPE_P(body, PM_BEGIN_NODE)) {
        pm_ybegin_stamp_end(body, def->end_keyword_loc);
        body->location = def->base.location;
        def->body = body;
    }
    else {
        def->body = (pm_node_t *) pm_ystatements_opt(p, body);
    }
    def->locals = pm_ylocals(p);

    if (args != NULL) {
        if (PM_NODE_TYPE_P(args, PM_PARAMETERS_NODE)) {
            def->parameters = (pm_parameters_node_t *) args;
        }
        else {
            YSTUB("pm_ydef_finish parameters");
        }
    }

    return node;
}

/* Claim the parameter-list parens for a def right after f_arglist reduces:
 * by the time the def closes, calls in the body will have reused the slot. */
static void
pm_ydef_parens(struct parser_params *p, NODE *node)
{
    if (!p->yparens.set || node == NULL || !PM_NODE_TYPE_P(node, PM_DEF_NODE)) return;
    pm_def_node_t *def = (pm_def_node_t *) node;
    def->lparen_loc = pm_yloc(&p->yparens.opening);
    def->rparen_loc = pm_yloc(&p->yparens.closing);
    p->yparens.set = 0;
}

/* An else clause, built at the opt_else reduction, which is the last moment
 * the `else` keyword's location exists; the enclosing if/unless/begin fills
 * in the end keyword when it closes. */
static NODE *
pm_yelse(struct parser_params *p, NODE *body, const YYLTYPE *else_loc, const YYLTYPE *loc)
{
    return (NODE *) pm_else_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(else_loc), pm_ystatements_opt(p, body), (pm_location_t) { 0 });
}

/* Attach the brackets to an array literal, and fold the static-literal flag
 * the way the hand-written parser does: an array of static literals is one. */
static NODE *
pm_yarray_brackets(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc)
{
    if (node == NULL || !PM_NODE_TYPE_P(node, PM_ARRAY_NODE)) {
        YSTUB("pm_yarray_brackets");
        return node;
    }

    pm_array_node_t *array = (pm_array_node_t *) node;
    array->opening_loc = pm_yloc(opening);
    array->closing_loc = pm_yloc(closing);
    array->base.location = pm_yloc(loc);

    bool is_static = true;
    for (size_t index = 0; index < array->elements.size; index++) {
        pm_node_t *element = array->elements.nodes[index];
        /* Containers do not count as static elements, matching prism. */
        if (!PM_NODE_FLAG_P(element, PM_NODE_FLAG_STATIC_LITERAL) ||
            PM_NODE_TYPE_P(element, PM_ARRAY_NODE) || PM_NODE_TYPE_P(element, PM_HASH_NODE)) {
            is_static = false;
            break;
        }
    }
    if (is_static) array->base.flags |= PM_NODE_FLAG_STATIC_LITERAL;

    return node;
}

/* A parenthesized expression: CRuby drops grouping parens (or marks a block),
 * prism keeps them as a node. */
static NODE *
pm_yparentheses(struct parser_params *p, NODE *body, const YYLTYPE *opening, const YYLTYPE *closing, const YYLTYPE *loc)
{
    pm_statements_node_t *statements = pm_ystatements_opt(p, body);
    pm_node_flags_t flags = 0;
    if (statements != NULL && statements->body.size > 1) flags = PM_PARENTHESES_NODE_FLAGS_MULTIPLE_STATEMENTS;
    return (NODE *) pm_parentheses_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        (pm_node_t *) statements, pm_yloc(opening), pm_yloc(closing));
}

/* Attach the keywords to a begin/end block once it closes. */
static NODE *
pm_ybegin_keywords(struct parser_params *p, NODE *node, const YYLTYPE *begin_loc, const YYLTYPE *end_loc)
{
    if (node != NULL && PM_NODE_TYPE_P(node, PM_BEGIN_NODE)) {
        pm_begin_node_t *begin = (pm_begin_node_t *) node;
        begin->begin_keyword_loc = pm_yloc(begin_loc);
        pm_ybegin_stamp_end(node, pm_yloc(end_loc));
    }
    return node;
}

/* An index call: a[i] and its write form. The brackets are the message. */
static NODE *
pm_yindex_call(struct parser_params *p, NODE *node, const YYLTYPE *opening, const YYLTYPE *closing)
{
    if (node != NULL && PM_NODE_TYPE_P(node, PM_CALL_NODE)) {
        pm_call_node_t *call = (pm_call_node_t *) node;
        call->opening_loc = pm_yloc(opening);
        call->closing_loc = pm_yloc(closing);
        call->message_loc = (pm_location_t) { opening->beg, closing->end - opening->beg };
    }
    return node;
}

/* Set the message location on a call once the operator/message token is at
 * hand; the constructors do not receive it. */
static NODE *
pm_ycall_message(NODE *node, const YYLTYPE *op_loc)
{
    if (node != NULL && PM_NODE_TYPE_P(node, PM_CALL_NODE)) {
        ((pm_call_node_t *) node)->message_loc = pm_yloc(op_loc);
    }
    return node;
}

/* Mirror of prism.c's pm_integer_arena_move (static there): a parsed integer
 * that spilled to the heap moves into the arena the node lives in. */
static void
pm_yinteger_arena_move(pm_arena_t *arena, pm_integer_t *integer)
{
    if (integer->values != NULL) {
        size_t byte_size = integer->length * sizeof(uint32_t);
        uint32_t *old_values = integer->values;
        integer->values = (uint32_t *) pm_arena_memdup(arena, old_values, byte_size, PRISM_ALIGNOF(uint32_t));
        xfree(old_values);
    }
}

/*
 * Statement sequences. CRuby chains statements through NODE_BLOCK; prism
 * gathers them in a StatementsNode. Anything that is not already a
 * StatementsNode is a single statement to be wrapped.
 */
static pm_statements_node_t *
pm_ystatements_ensure(struct parser_params *p, NODE *node)
{
    if (node == NULL) {
        return pm_statements_node_new(p->pm->arena, ++p->pm->node_id, 0, (pm_location_t) { 0 }, (pm_node_list_t) { 0 });
    }
    if (PM_NODE_TYPE_P(node, PM_STATEMENTS_NODE)) {
        return (pm_statements_node_t *) node;
    }

    pm_node_list_t body = { 0 };
    node->flags |= PM_NODE_FLAG_NEWLINE;
    pm_node_list_append(p->pm->arena, &body, node);
    return pm_statements_node_new(p->pm->arena, ++p->pm->node_id, 0, node->location, body);
}

static rb_node_scope_t *
rb_node_scope_new(struct parser_params *p, rb_node_args_t *nd_args, NODE *nd_body, NODE *nd_parent, const YYLTYPE *loc)
{
    pm_constant_id_list_t locals = pm_ylocals(p);

    if (nd_args != NULL || nd_parent != NULL) {
        /* Class/module/def scopes arrive with their node ports. */
        YSTUB("rb_node_scope_new");
    }

    pm_statements_node_t *body = pm_ystatements_ensure(p, nd_body);
    return (rb_node_scope_t *) pm_program_node_new(p->pm->arena, ++p->pm->node_id, 0, body->base.location, locals, body);
}

static rb_node_scope_t *
rb_node_scope_new2(struct parser_params *p, rb_ast_id_table_t *nd_tbl, rb_node_args_t *nd_args, NODE *nd_body, NODE *nd_parent, const YYLTYPE *loc)
{
    YSTUB("rb_node_scope_new2");
    return NULL;
}

static rb_node_defn_t *
rb_node_defn_new(struct parser_params *p, ID nd_mid, NODE *nd_defn, const YYLTYPE *loc)
{
    (void) nd_defn;
    pm_location_t zero = { 0 };
    return (rb_node_defn_t *) pm_def_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        YID2CONST(nd_mid), zero, NULL, NULL, NULL, (pm_constant_id_list_t) { 0 },
        zero, zero, zero, zero, zero, zero);
}

static rb_node_defs_t *
rb_node_defs_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_defn, const YYLTYPE *loc)
{
    (void) nd_defn;
    pm_location_t zero = { 0 };
    return (rb_node_defs_t *) pm_def_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        YID2CONST(nd_mid), zero, nd_recv, NULL, NULL, (pm_constant_id_list_t) { 0 },
        zero, zero, zero, zero, zero, zero);
}

static rb_node_block_t *
rb_node_block_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc)
{
    return (rb_node_block_t *) pm_ystatements_ensure(p, nd_head);
}

static rb_node_for_t *
rb_node_for_new(struct parser_params *p, NODE *nd_iter, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *for_keyword_loc, const YYLTYPE *in_keyword_loc, const YYLTYPE *do_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    YSTUB("rb_node_for_new");
    return NULL;
}

static rb_node_for_masgn_t *
rb_node_for_masgn_new(struct parser_params *p, NODE *nd_var, const YYLTYPE *loc)
{
    YSTUB("rb_node_for_masgn_new");
    return NULL;
}

static rb_node_retry_t *
rb_node_retry_new(struct parser_params *p, const YYLTYPE *loc)
{
    YSTUB("rb_node_retry_new");
    return NULL;
}

static rb_node_begin_t *
rb_node_begin_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc)
{
    /* A bodystmt with rescue/else/ensure already built the BeginNode; the
     * keywords are stamped by the enclosing begin/end reduction. */
    if (nd_body != NULL && PM_NODE_TYPE_P(nd_body, PM_BEGIN_NODE)) {
        nd_body->location = pm_yloc(loc);
        return (rb_node_begin_t *) nd_body;
    }

    return (rb_node_begin_t *) pm_begin_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        (pm_location_t) { 0 }, pm_ystatements_opt(p, nd_body),
        NULL, NULL, NULL, (pm_location_t) { 0 });
}

static rb_node_rescue_t *
rb_node_rescue_new(struct parser_params *p, NODE *nd_head, NODE *nd_resq, NODE *nd_else, const YYLTYPE *loc)
{
    YSTUB("rb_node_rescue_new");
    return NULL;
}

static rb_node_resbody_t *
rb_node_resbody_new(struct parser_params *p, NODE *nd_args, NODE *nd_exc_var, NODE *nd_body, NODE *nd_next, const YYLTYPE *loc)
{
    pm_node_list_t exceptions = { 0 };
    if (nd_args != NULL) {
        if (PM_NODE_TYPE_P(nd_args, PM_ARRAY_NODE)) {
            exceptions = ((pm_array_node_t *) nd_args)->elements;
        }
        else {
            YSTUB("rb_node_resbody_new");
        }
    }

    if (nd_next != NULL && !PM_NODE_TYPE_P(nd_next, PM_RESCUE_NODE)) nd_next = NULL;

    return (rb_node_resbody_t *) pm_rescue_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        (pm_location_t) { 0 }, exceptions, (pm_location_t) { 0 },
        nd_exc_var, (pm_location_t) { 0 },
        pm_ystatements_opt(p, nd_body), (pm_rescue_node_t *) nd_next);
}

static rb_node_ensure_t *
rb_node_ensure_new(struct parser_params *p, NODE *nd_head, NODE *nd_ensr, const YYLTYPE *loc)
{
    YSTUB("rb_node_ensure_new");
    return NULL;
}

static rb_node_and_t *
rb_node_and_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc, const YYLTYPE *operator_loc)
{
    return (rb_node_and_t *) pm_and_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        nd_1st, nd_2nd, pm_yloc(operator_loc));
}

static rb_node_or_t *
rb_node_or_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc, const YYLTYPE *operator_loc)
{
    return (rb_node_or_t *) pm_or_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        nd_1st, nd_2nd, pm_yloc(operator_loc));
}

static rb_node_return_t *
rb_node_return_new(struct parser_params *p, NODE *nd_stts, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    return (rb_node_return_t *) pm_return_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(keyword_loc), pm_yargs_from_list(p, nd_stts));
}

static rb_node_yield_t *
rb_node_yield_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *lparen_loc, const YYLTYPE *rparen_loc)
{
    return (rb_node_yield_t *) pm_yield_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(keyword_loc), pm_yloc(lparen_loc),
        pm_yargs_from_list(p, nd_head), pm_yloc(rparen_loc));
}

static rb_node_if_t *
rb_node_if_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, NODE *nd_else, const YYLTYPE *loc, const YYLTYPE* if_keyword_loc, const YYLTYPE* then_keyword_loc, const YYLTYPE* end_keyword_loc)
{
    pm_node_t *subsequent = nd_else;
    pm_location_t end_keyword = pm_yloc(end_keyword_loc);
    for (pm_node_t *chain = subsequent; chain != NULL;) {
        if (end_keyword.length > 0) {
            uint32_t end = end_keyword.start + end_keyword.length;
            if (end > chain->location.start + chain->location.length) {
                chain->location.length = end - chain->location.start;
            }
        }
        if (PM_NODE_TYPE_P(chain, PM_ELSE_NODE)) {
            ((pm_else_node_t *) chain)->end_keyword_loc = end_keyword;
            break;
        }
        else if (PM_NODE_TYPE_P(chain, PM_IF_NODE)) {
            pm_if_node_t *nested = (pm_if_node_t *) chain;
            nested->end_keyword_loc = end_keyword;
            chain = nested->subsequent;
        }
        else {
            break;
        }
    }
    return (rb_node_if_t *) pm_if_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(if_keyword_loc), nd_cond, pm_ythen_loc(p, then_keyword_loc),
        pm_ystatements_opt(p, nd_body), subsequent, end_keyword);
}

static rb_node_unless_t *
rb_node_unless_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, NODE *nd_else, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *then_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    pm_else_node_t *else_clause = NULL;
    pm_location_t end_keyword = pm_yloc(end_keyword_loc);
    if (nd_else != NULL && PM_NODE_TYPE_P(nd_else, PM_ELSE_NODE)) {
        else_clause = (pm_else_node_t *) nd_else;
        else_clause->end_keyword_loc = end_keyword;
        if (end_keyword.length > 0) {
            uint32_t end = end_keyword.start + end_keyword.length;
            if (end > else_clause->base.location.start + else_clause->base.location.length) {
                else_clause->base.location.length = end - else_clause->base.location.start;
            }
        }
    }
    else if (nd_else != NULL) {
        YSTUB("rb_node_unless_new");
    }
    return (rb_node_unless_t *) pm_unless_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(keyword_loc), nd_cond, pm_ythen_loc(p, then_keyword_loc),
        pm_ystatements_opt(p, nd_body), else_clause, end_keyword);
}

static rb_node_class_t *
rb_node_class_new(struct parser_params *p, NODE *nd_cpath, NODE *nd_body, NODE *nd_super, const YYLTYPE *loc, const YYLTYPE *class_keyword_loc, const YYLTYPE *inheritance_operator_loc, const YYLTYPE *end_keyword_loc)
{
    pm_constant_id_list_t locals = pm_ylocals(p);
    return (rb_node_class_t *) pm_class_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), locals,
        pm_yloc(class_keyword_loc), nd_cpath, pm_yloc(inheritance_operator_loc),
        nd_super, pm_yclass_body(p, nd_body, loc, end_keyword_loc),
        pm_yloc(end_keyword_loc), pm_yconstant_path_name(nd_cpath));
}

static rb_node_sclass_t *
rb_node_sclass_new(struct parser_params *p, NODE *nd_recv, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *class_keyword_loc, const YYLTYPE *operator_loc, const YYLTYPE *end_keyword_loc)
{
    pm_constant_id_list_t locals = pm_ylocals(p);
    return (rb_node_sclass_t *) pm_singleton_class_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), locals,
        pm_yloc(class_keyword_loc), pm_yloc(operator_loc), nd_recv,
        pm_yclass_body(p, nd_body, loc, end_keyword_loc), pm_yloc(end_keyword_loc));
}

static rb_node_module_t *
rb_node_module_new(struct parser_params *p, NODE *nd_cpath, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *module_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    pm_constant_id_list_t locals = pm_ylocals(p);
    return (rb_node_module_t *) pm_module_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), locals,
        pm_yloc(module_keyword_loc), nd_cpath,
        pm_yclass_body(p, nd_body, loc, end_keyword_loc),
        pm_yloc(end_keyword_loc), pm_yconstant_path_name(nd_cpath));
}

static rb_node_iter_t *
rb_node_iter_new(struct parser_params *p, rb_node_args_t *nd_args, NODE *nd_body, const YYLTYPE *loc)
{
    pm_node_t *body;
    if (nd_body != NULL && PM_NODE_TYPE_P(nd_body, PM_BEGIN_NODE)) {
        /* A body that grew rescue/ensure clauses hangs directly off the
         * block, sharing its span once the braces are known. */
        body = nd_body;
    }
    else {
        body = (pm_node_t *) pm_ystatements_opt(p, nd_body);
    }
    return (rb_node_iter_t *) pm_block_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_ylocals(p), (pm_node_t *) nd_args, body,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_lambda_t *
rb_node_lambda_new(struct parser_params *p, rb_node_args_t *nd_args, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *operator_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc)
{
    pm_node_t *body;
    if (nd_body != NULL && PM_NODE_TYPE_P(nd_body, PM_BEGIN_NODE)) {
        /* rescue/ensure clauses hang directly off the lambda, spanning the
         * whole braced body with the end keyword stamped, as in blocks */
        body = nd_body;
        pm_location_t closing = pm_yloc(closing_loc);
        pm_ybegin_stamp_end(body, closing);
        body->location = (pm_location_t) { opening_loc->beg, closing_loc->end - opening_loc->beg };
    }
    else {
        body = (pm_node_t *) pm_ystatements_opt(p, nd_body);
    }

    return (rb_node_lambda_t *) pm_lambda_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_ylocals(p), pm_yloc(operator_loc), pm_yloc(opening_loc), pm_yloc(closing_loc),
        (pm_node_t *) nd_args, body);
}

static rb_node_case_t *
rb_node_case_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    return (rb_node_case_t *) pm_ycase(p, nd_head, nd_body, loc, case_keyword_loc, end_keyword_loc);
}

static rb_node_case2_t *
rb_node_case2_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    return (rb_node_case2_t *) pm_ycase(p, NULL, nd_body, loc, case_keyword_loc, end_keyword_loc);
}

static rb_node_case3_t *
rb_node_case3_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *case_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    YSTUB("rb_node_case3_new");
    return NULL;
}

static rb_node_when_t *
rb_node_when_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, NODE *nd_next, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *then_keyword_loc)
{
    pm_node_list_t conditions = { 0 };
    if (nd_head != NULL && PM_NODE_TYPE_P(nd_head, PM_ARRAY_NODE)) {
        conditions = ((pm_array_node_t *) nd_head)->elements;
    }
    else if (nd_head != NULL) {
        pm_node_list_append(p->pm->arena, &conditions, nd_head);
    }

    pm_location_t keyword = pm_yloc(keyword_loc);
    pm_location_t then_keyword = pm_ythen_loc(p, then_keyword_loc);

    pm_statements_node_t *statements = pm_ystatements_opt(p, nd_body);

    /* the clause's own span: keyword through its own body */
    uint32_t end = keyword.start + keyword.length;
    if (statements != NULL) end = statements->base.location.start + statements->base.location.length;
    else if (then_keyword.length > 0) end = then_keyword.start + then_keyword.length;
    else if (conditions.size > 0) {
        pm_node_t *last = conditions.nodes[conditions.size - 1];
        end = last->location.start + last->location.length;
    }

    pm_node_t *when = (pm_node_t *) pm_when_node_new(
        p->pm->arena, ++p->pm->node_id, 0, (pm_location_t) { keyword.start, end - keyword.start },
        keyword, conditions, then_keyword, statements);

    /* Clauses collect in a carrier: this when first, then whatever follows
     * (more whens, or the else as the last element). */
    pm_node_list_t clauses = { 0 };
    pm_node_list_append(p->pm->arena, &clauses, when);
    if (nd_next != NULL) {
        if (PM_NODE_TYPE_P(nd_next, PM_ARRAY_NODE)) {
            pm_array_node_t *rest = (pm_array_node_t *) nd_next;
            for (size_t i = 0; i < rest->elements.size; i++) {
                pm_node_list_append(p->pm->arena, &clauses, rest->elements.nodes[i]);
            }
        }
        else {
            pm_node_list_append(p->pm->arena, &clauses, nd_next);
        }
    }

    return (rb_node_when_t *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, when->location, clauses,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_in_t *
rb_node_in_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, NODE *nd_next, const YYLTYPE *loc, const YYLTYPE *in_keyword_loc, const YYLTYPE *then_keyword_loc, const YYLTYPE *operator_loc)
{
    YSTUB("rb_node_in_new");
    return NULL;
}

static rb_node_while_t *
rb_node_while_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, long nd_state, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *closing_loc)
{
    pm_node_flags_t flags = nd_state == 0 ? PM_LOOP_FLAGS_BEGIN_MODIFIER : 0;
    pm_location_t do_loc = { 0 };
    if (p->ydo.set) { do_loc = pm_yloc(&p->ydo.loc); p->ydo.set = 0; }
    return (rb_node_while_t *) pm_while_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        pm_yloc(keyword_loc), do_loc, pm_yloc(closing_loc),
        nd_cond, pm_ystatements_opt(p, nd_body));
}

static rb_node_until_t *
rb_node_until_new(struct parser_params *p, NODE *nd_cond, NODE *nd_body, long nd_state, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *closing_loc)
{
    pm_node_flags_t flags = nd_state == 0 ? PM_LOOP_FLAGS_BEGIN_MODIFIER : 0;
    pm_location_t do_loc = { 0 };
    if (p->ydo.set) { do_loc = pm_yloc(&p->ydo.loc); p->ydo.set = 0; }
    return (rb_node_until_t *) pm_until_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        pm_yloc(keyword_loc), do_loc, pm_yloc(closing_loc),
        nd_cond, pm_ystatements_opt(p, nd_body));
}

static rb_node_colon2_t *
rb_node_colon2_new(struct parser_params *p, NODE *nd_head, ID nd_mid, const YYLTYPE *loc, const YYLTYPE *delimiter_loc, const YYLTYPE *name_loc)
{
    if (nd_head == NULL && delimiter_loc->end == delimiter_loc->beg) {
        return (rb_node_colon2_t *) pm_constant_read_node_new(
            p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_mid));
    }
    return (rb_node_colon2_t *) pm_constant_path_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        nd_head, YID2CONST(nd_mid), pm_yloc(delimiter_loc), pm_yloc(name_loc));
}

static rb_node_colon3_t *
rb_node_colon3_new(struct parser_params *p, ID nd_mid, const YYLTYPE *loc, const YYLTYPE *delimiter_loc, const YYLTYPE *name_loc)
{
    return (rb_node_colon3_t *) pm_constant_path_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        NULL, YID2CONST(nd_mid), pm_yloc(delimiter_loc), pm_yloc(name_loc));
}

static rb_node_dot2_t *
rb_node_dot2_new(struct parser_params *p, NODE *nd_beg, NODE *nd_end, const YYLTYPE *loc, const YYLTYPE *operator_loc)
{
    pm_node_flags_t flags = 0;
    if ((nd_beg == NULL || PM_NODE_FLAG_P(nd_beg, PM_NODE_FLAG_STATIC_LITERAL)) &&
        (nd_end == NULL || PM_NODE_FLAG_P(nd_end, PM_NODE_FLAG_STATIC_LITERAL))) {
        flags |= PM_NODE_FLAG_STATIC_LITERAL;
    }
    return (rb_node_dot2_t *) pm_range_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        nd_beg, nd_end, pm_yloc(operator_loc));
}

static rb_node_dot3_t *
rb_node_dot3_new(struct parser_params *p, NODE *nd_beg, NODE *nd_end, const YYLTYPE *loc, const YYLTYPE *operator_loc)
{
    pm_node_flags_t flags = PM_RANGE_FLAGS_EXCLUDE_END;
    if ((nd_beg == NULL || PM_NODE_FLAG_P(nd_beg, PM_NODE_FLAG_STATIC_LITERAL)) &&
        (nd_end == NULL || PM_NODE_FLAG_P(nd_end, PM_NODE_FLAG_STATIC_LITERAL))) {
        flags |= PM_NODE_FLAG_STATIC_LITERAL;
    }
    return (rb_node_dot3_t *) pm_range_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        nd_beg, nd_end, pm_yloc(operator_loc));
}

static rb_node_self_t *
rb_node_self_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_self_t *) pm_self_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc));
}

static rb_node_nil_t *
rb_node_nil_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_nil_t *) pm_nil_node_new(p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc));
}

static rb_node_true_t *
rb_node_true_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_true_t *) pm_true_node_new(p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc));
}

static rb_node_false_t *
rb_node_false_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_false_t *) pm_false_node_new(p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc));
}

static rb_node_super_t *
rb_node_super_new(struct parser_params *p, NODE *nd_args, const YYLTYPE *loc,
                  const YYLTYPE *keyword_loc, const YYLTYPE *lparen_loc, const YYLTYPE *rparen_loc)
{
    pm_node_t *block = p->yblock_pass;
    p->yblock_pass = NULL;
    return (rb_node_super_t *) pm_super_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(keyword_loc), pm_yloc(lparen_loc),
        pm_yargs_from_list(p, nd_args), pm_yloc(rparen_loc), block);
}

static rb_node_zsuper_t *
rb_node_zsuper_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_zsuper_t *) pm_forwarding_super_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(loc), NULL);
}

static rb_node_match2_t *
rb_node_match2_new(struct parser_params *p, NODE *nd_recv, NODE *nd_value, const YYLTYPE *loc)
{
    YSTUB("rb_node_match2_new");
    return NULL;
}

static rb_node_match3_t *
rb_node_match3_new(struct parser_params *p, NODE *nd_recv, NODE *nd_value, const YYLTYPE *loc)
{
    YSTUB("rb_node_match3_new");
    return NULL;
}

static rb_node_list_t *
rb_node_list_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc)
{
    pm_node_list_t elements = { 0 };
    if (nd_head != NULL) pm_node_list_append(p->pm->arena, &elements, nd_head);
    return (rb_node_list_t *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), elements,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_list_t *
rb_node_list_new2(struct parser_params *p, NODE *nd_head, long nd_alen, NODE *nd_next, const YYLTYPE *loc)
{
    YSTUB("rb_node_list_new2");
    return NULL;
}

static rb_node_zlist_t *
rb_node_zlist_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_zlist_t *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        (pm_node_list_t) { 0 }, (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_hash_t *
rb_node_hash_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc)
{
    YSTUB("rb_node_hash_new");
    return NULL;
}

static rb_node_masgn_t *
rb_node_masgn_new(struct parser_params *p, NODE *nd_head, NODE *nd_args, const YYLTYPE *loc)
{
    pm_location_t location = pm_yloc(loc);

    pm_node_list_t lefts = { 0 };
    if (nd_head != NULL && PM_NODE_TYPE_P(nd_head, PM_ARRAY_NODE)) {
        pm_node_list_t items = ((pm_array_node_t *) nd_head)->elements;
        for (size_t i = 0; i < items.size; i++) {
            pm_node_list_append(p->pm->arena, &lefts, pm_ytarget(p, items.nodes[i]));
        }
    }

    /* a postarg carrier splits into the rest and the trailing targets */
    NODE *rest_node = nd_args;
    pm_node_list_t rights = { 0 };
    if (nd_args != NULL && !NODE_NAMED_REST_P(nd_args)) {
        /* NODE_SPECIAL_NO_NAME_REST: a bare star */
        rest_node = NODE_SPECIAL_NO_NAME_REST;
    }
    else if (nd_args != NULL && PM_NODE_TYPE_P(nd_args, PM_ARRAY_NODE)) {
        pm_node_list_t parts = ((pm_array_node_t *) nd_args)->elements;
        rest_node = (NODE *) parts.nodes[0];
        NODE *posts = (NODE *) parts.nodes[1];
        if (posts != NULL && PM_NODE_TYPE_P(posts, PM_ARRAY_NODE)) {
            pm_node_list_t items = ((pm_array_node_t *) posts)->elements;
            for (size_t i = 0; i < items.size; i++) {
                pm_node_list_append(p->pm->arena, &rights, pm_ytarget(p, items.nodes[i]));
            }
        }
    }

    pm_node_t *rest = NULL;
    if (rest_node != NULL) {
        /* the star sits between the last left (or the start) and the rest's
         * own name (or the first post, or the end); nothing else in that
         * range can be a star */
        uint32_t lo = location.start;
        if (lefts.size > 0) {
            pm_node_t *last = lefts.nodes[lefts.size - 1];
            lo = last->location.start + last->location.length;
        }
        uint32_t hi;
        if (NODE_NAMED_REST_P(rest_node)) hi = rest_node->location.start;
        else if (rights.size > 0) hi = rights.nodes[0]->location.start;
        else hi = location.start + location.length;

        pm_location_t star = { 0 };
        for (uint32_t scan = lo; scan < hi; scan++) {
            if (p->pm->start[scan] == '*') { star = (pm_location_t) { scan, 1 }; break; }
        }

        if (NODE_NAMED_REST_P(rest_node)) {
            NODE *expression = pm_ytarget(p, rest_node);
            pm_location_t splat_loc = star;
            if (expression != NULL) {
                splat_loc.length = (expression->location.start + expression->location.length) - splat_loc.start;
            }
            rest = (pm_node_t *) pm_splat_node_new(
                p->pm->arena, ++p->pm->node_id, 0, splat_loc, star, expression);
        }
        else {
            rest = (pm_node_t *) pm_splat_node_new(
                p->pm->arena, ++p->pm->node_id, 0, star, star, NULL);
        }
    }
    else if (location.length > 0 && p->pm->start[location.start + location.length - 1] == ',') {
        /* a trailing comma is an implicit rest: a, = value */
        pm_location_t comma = { location.start + location.length - 1, 1 };
        rest = (pm_node_t *) pm_implicit_rest_node_new(p->pm->arena, ++p->pm->node_id, 0, comma);
    }

    return (rb_node_masgn_t *) pm_multi_target_node_new(
        p->pm->arena, ++p->pm->node_id, 0, location,
        lefts, rest, rights, (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_gasgn_t *
rb_node_gasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc)
{
    pm_location_t name_loc = pm_yloc(loc);
    return (NODE *) pm_global_variable_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, name_loc,
        YID2CONST(nd_vid), name_loc, nd_value, (pm_location_t) { 0 });
}

static rb_node_lasgn_t *
rb_node_lasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc)
{
    pm_location_t name_loc = pm_yloc(loc);
    return (NODE *) pm_local_variable_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, name_loc,
        YID2CONST(nd_vid), 0, name_loc, nd_value, (pm_location_t) { 0 });
}

static rb_node_dasgn_t *
rb_node_dasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc)
{
    pm_location_t name_loc = pm_yloc(loc);
    return (NODE *) pm_local_variable_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, name_loc,
        YID2CONST(nd_vid), pm_ydvar_depth(p, nd_vid), name_loc, nd_value, (pm_location_t) { 0 });
}

static rb_node_iasgn_t *
rb_node_iasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc)
{
    pm_location_t name_loc = pm_yloc(loc);
    return (NODE *) pm_instance_variable_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, name_loc,
        YID2CONST(nd_vid), name_loc, nd_value, (pm_location_t) { 0 });
}

static rb_node_cvasgn_t *
rb_node_cvasgn_new(struct parser_params *p, ID nd_vid, NODE *nd_value, const YYLTYPE *loc)
{
    pm_location_t name_loc = pm_yloc(loc);
    return (NODE *) pm_class_variable_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, name_loc,
        YID2CONST(nd_vid), name_loc, nd_value, (pm_location_t) { 0 });
}

static rb_node_op_asgn1_t *
rb_node_op_asgn1_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *index, NODE *rvalue, const YYLTYPE *loc, const YYLTYPE *call_operator_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc, const YYLTYPE *binary_operator_loc)
{
    YSTUB("rb_node_op_asgn1_new");
    return NULL;
}

static rb_node_op_asgn2_t *
rb_node_op_asgn2_new(struct parser_params *p, NODE *nd_recv, NODE *nd_value, ID nd_vid, ID nd_mid, bool nd_aid, const YYLTYPE *loc, const YYLTYPE *call_operator_loc, const YYLTYPE *message_loc, const YYLTYPE *binary_operator_loc)
{
    YSTUB("rb_node_op_asgn2_new");
    return NULL;
}

static rb_node_op_asgn_or_t *
rb_node_op_asgn_or_new(struct parser_params *p, NODE *nd_head, NODE *nd_value, const YYLTYPE *loc)
{
    YSTUB("rb_node_op_asgn_or_new");
    return NULL;
}

static rb_node_op_asgn_and_t *
rb_node_op_asgn_and_new(struct parser_params *p, NODE *nd_head, NODE *nd_value, const YYLTYPE *loc)
{
    YSTUB("rb_node_op_asgn_and_new");
    return NULL;
}

static rb_node_gvar_t *
rb_node_gvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc)
{
    return (rb_node_gvar_t *) pm_global_variable_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_vid));
}

static rb_node_lvar_t *
rb_node_lvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc)
{
    /* the anonymous forwarding markers read as an absent expression */
    if (nd_vid == idFWD_REST || nd_vid == idFWD_KWREST || nd_vid == idFWD_BLOCK) return NULL;
    return (rb_node_lvar_t *) pm_local_variable_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_vid), 0);
}

static rb_node_dvar_t *
rb_node_dvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc)
{
    return (rb_node_dvar_t *) pm_local_variable_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_vid), pm_ydvar_depth(p, nd_vid));
}

static rb_node_ivar_t *
rb_node_ivar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc)
{
    return (rb_node_ivar_t *) pm_instance_variable_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_vid));
}

static rb_node_const_t *
rb_node_const_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc)
{
    return (rb_node_const_t *) pm_constant_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_vid));
}

static rb_node_cvar_t *
rb_node_cvar_new(struct parser_params *p, ID nd_vid, const YYLTYPE *loc)
{
    return (rb_node_cvar_t *) pm_class_variable_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(nd_vid));
}

static rb_node_nth_ref_t *
rb_node_nth_ref_new(struct parser_params *p, long nd_nth, const YYLTYPE *loc)
{
    return (rb_node_nth_ref_t *) pm_numbered_reference_read_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), (uint32_t) nd_nth);
}

static rb_node_back_ref_t *
rb_node_back_ref_new(struct parser_params *p, long nd_nth, const YYLTYPE *loc)
{
    /* The pool keeps pointers, so the two-byte name must not live on the
     * stack; intern through the copying path. */
    char name[3] = { '$', (char) nd_nth, '\0' };
    ID id = pm_yid_intern(&p->pm->metadata_arena, &p->pm->constant_pool, (const uint8_t *) name, 2, p->enc);
    return (rb_node_back_ref_t *) pm_back_reference_read_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), YID2CONST(id));
}

static rb_node_integer_t *
rb_node_integer_new(struct parser_params *p, char* val, int base, const YYLTYPE *loc)
{
    xfree(val);

    pm_node_flags_t flags = PM_NODE_FLAG_STATIC_LITERAL;
    pm_integer_base_t integer_base;
    switch (base) {
      case 2: flags |= PM_INTEGER_BASE_FLAGS_BINARY; integer_base = PM_INTEGER_BASE_BINARY; break;
      case 8: flags |= PM_INTEGER_BASE_FLAGS_OCTAL; integer_base = PM_INTEGER_BASE_OCTAL; break;
      case 16: flags |= PM_INTEGER_BASE_FLAGS_HEXADECIMAL; integer_base = PM_INTEGER_BASE_HEXADECIMAL; break;
      default: flags |= PM_INTEGER_BASE_FLAGS_DECIMAL; integer_base = PM_INTEGER_BASE_DECIMAL; break;
    }

    pm_integer_node_t *node = pm_integer_node_new(p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc), ((pm_integer_t) { 0 }));
    pm_integer_parse(&node->value, integer_base, p->pm->start + loc->beg, p->pm->start + loc->end);
    pm_yinteger_arena_move(p->pm->arena, &node->value);
    return (rb_node_integer_t *) node;
}

static rb_node_float_t *
rb_node_float_new(struct parser_params *p, char* val, const YYLTYPE *loc)
{
    /* the lexer's token buffer already has the underscores stripped */
    double value = strtod(val, NULL);
    xfree(val);
    return (rb_node_float_t *) pm_float_node_new(
        p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc), value);
}

static rb_node_rational_t *
rb_node_rational_new(struct parser_params *p, char* val, int base, int seen_point, const YYLTYPE *loc)
{
    xfree(val);

    pm_node_flags_t flags = PM_NODE_FLAG_STATIC_LITERAL;
    pm_integer_base_t integer_base;
    switch (base) {
      case 2: flags |= PM_INTEGER_BASE_FLAGS_BINARY; integer_base = PM_INTEGER_BASE_BINARY; break;
      case 8: flags |= PM_INTEGER_BASE_FLAGS_OCTAL; integer_base = PM_INTEGER_BASE_OCTAL; break;
      case 16: flags |= PM_INTEGER_BASE_FLAGS_HEXADECIMAL; integer_base = PM_INTEGER_BASE_HEXADECIMAL; break;
      default: flags |= PM_INTEGER_BASE_FLAGS_DECIMAL; integer_base = PM_INTEGER_BASE_DECIMAL; break;
    }

    pm_rational_node_t *node = pm_rational_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        ((pm_integer_t) { 0 }), ((pm_integer_t) { 0 }));

    /* the token in the source is <number>r */
    const uint8_t *start = p->pm->start + loc->beg;
    const uint8_t *end = p->pm->start + loc->end - 1;

    if (!seen_point) {
        pm_integer_parse(&node->numerator, integer_base, start, end);
        node->denominator.value = 1;
    }
    else {
        /* mirrors pm_float_node_rational_create in src/prism.c */
        while (start < end && *start == '0') start++;
        while (end > start && end[-1] == '0') end--;

        size_t length = (size_t) (end - start);
        if (length == 1) {
            node->denominator.value = 1;
            return (rb_node_rational_t *) node;
        }

        const uint8_t *point = memchr(start, '.', length);

        uint8_t *digits = xmalloc(length);
        if (digits == NULL) abort();

        memcpy(digits, start, (size_t) (point - start));
        memcpy(digits + (point - start), point + 1, (size_t) (end - point - 1));
        pm_integer_parse(&node->numerator, PM_INTEGER_BASE_DEFAULT, digits, digits + length - 1);

        size_t fract_length = 0;
        for (const uint8_t *fract = point; fract < end; ++fract) {
            if (*fract != '_') ++fract_length;
        }
        digits[0] = '1';
        if (fract_length > 1) memset(digits + 1, '0', fract_length - 1);
        pm_integer_parse(&node->denominator, PM_INTEGER_BASE_DEFAULT, digits, digits + fract_length);
        xfree(digits);

        pm_integers_reduce(&node->numerator, &node->denominator);
    }

    pm_yinteger_arena_move(p->pm->arena, &node->numerator);
    pm_yinteger_arena_move(p->pm->arena, &node->denominator);
    return (rb_node_rational_t *) node;
}

static rb_node_imaginary_t *
rb_node_imaginary_new(struct parser_params *p, char* val, int base, int seen_point, enum rb_numeric_type numeric_type, const YYLTYPE *loc)
{
    /* the numeric child ends before the trailing i; it takes over val */
    YYLTYPE numeric_loc = *loc;
    numeric_loc.end -= 1;

    NODE *numeric;
    switch (numeric_type) {
      case integer_literal:
        numeric = (NODE *) rb_node_integer_new(p, val, base, &numeric_loc);
        break;
      case float_literal:
        numeric = (NODE *) rb_node_float_new(p, val, &numeric_loc);
        break;
      default:
        numeric = (NODE *) rb_node_rational_new(p, val, base, seen_point, &numeric_loc);
        break;
    }

    return (rb_node_imaginary_t *) pm_imaginary_node_new(
        p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc), numeric);
}

static rb_node_str_t *
rb_node_str_new(struct parser_params *p, rb_parser_string_t *string, const YYLTYPE *loc)
{
    pm_location_t content_loc = pm_yloc(loc);
    return (rb_node_str_t *) pm_string_node_new(
        p->pm->arena, ++p->pm->node_id, 0, content_loc,
        (pm_location_t) { 0 }, content_loc, (pm_location_t) { 0 },
        pm_ystr_take(p, string));
}

/* TODO; Use union for NODE_DSTR2 */
static rb_node_dstr_t *
rb_node_dstr_new0(struct parser_params *p, rb_parser_string_t *string, long nd_alen, NODE *nd_next, const YYLTYPE *loc)
{
    YSTUB("rb_node_dstr_new0");
    return NULL;
}

static rb_node_dstr_t *
rb_node_dstr_new(struct parser_params *p, rb_parser_string_t *string, const YYLTYPE *loc)
{
    YSTUB("rb_node_dstr_new");
    return NULL;
}

static rb_node_xstr_t *
rb_node_xstr_new(struct parser_params *p, rb_parser_string_t *string, const YYLTYPE *loc)
{
    YSTUB("rb_node_xstr_new");
    return NULL;
}

static rb_node_dxstr_t *
rb_node_dxstr_new(struct parser_params *p, rb_parser_string_t *string, long nd_alen, NODE *nd_next, const YYLTYPE *loc)
{
    YSTUB("rb_node_dxstr_new");
    return NULL;
}

static rb_node_sym_t *
rb_node_sym_new(struct parser_params *p, rb_parser_string_t *str, const YYLTYPE *loc)
{
    pm_location_t location = pm_yloc(loc);
    pm_location_t opening_loc = { 0 };
    pm_location_t value_loc = location;

    if (location.length > 0 && p->pm->start[location.start] == ':') {
        opening_loc = (pm_location_t) { location.start, 1 };
        value_loc = (pm_location_t) { location.start + 1, location.length - 1 };
    }

    pm_node_flags_t flags = PM_NODE_FLAG_STATIC_LITERAL;
    if (str == NULL || pm_ystring_coderange(str) == PM_YSTRING_CODERANGE_7BIT) {
        flags |= PM_SYMBOL_FLAGS_FORCED_US_ASCII_ENCODING;
    }

    return (rb_node_sym_t *) pm_symbol_node_new(
        p->pm->arena, ++p->pm->node_id, flags, location,
        opening_loc, value_loc, (pm_location_t) { 0 },
        str == NULL ? PM_STRING_EMPTY : pm_ystr_take(p, str));
}

static rb_node_dsym_t *
rb_node_dsym_new(struct parser_params *p, rb_parser_string_t *string, long nd_alen, NODE *nd_next, const YYLTYPE *loc)
{
    YSTUB("rb_node_dsym_new");
    return NULL;
}

static rb_node_evstr_t *
rb_node_evstr_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc)
{
    /* #$ivar / #@ivar embed a variable with no braces; the opening token is
     * the lone `#`. Everything else is #{...} embedded statements. */
    if (opening_loc->end - opening_loc->beg == 1 && nd_body != NULL &&
        (PM_NODE_TYPE_P(nd_body, PM_INSTANCE_VARIABLE_READ_NODE) ||
         PM_NODE_TYPE_P(nd_body, PM_GLOBAL_VARIABLE_READ_NODE) ||
         PM_NODE_TYPE_P(nd_body, PM_CLASS_VARIABLE_READ_NODE) ||
         PM_NODE_TYPE_P(nd_body, PM_BACK_REFERENCE_READ_NODE) ||
         PM_NODE_TYPE_P(nd_body, PM_NUMBERED_REFERENCE_READ_NODE))) {
        return (rb_node_evstr_t *) pm_embedded_variable_node_new(
            p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
            pm_yloc(opening_loc), nd_body);
    }

    pm_statements_node_t *statements = pm_ystatements_opt(p, nd_body);
    /* A lone expression in an interpolation is not a line start (the wrap
     * marks it as one); with multiple statements they all are, as usual. */
    if (statements != NULL && statements->body.size == 1) {
        statements->body.nodes[0]->flags &= (pm_node_flags_t) ~PM_NODE_FLAG_NEWLINE;
    }
    return (rb_node_evstr_t *) pm_embedded_statements_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yloc(opening_loc), statements, pm_yloc(closing_loc));
}

static rb_node_regx_t *
rb_node_regx_new(struct parser_params *p, rb_parser_string_t *string, int options, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *content_loc, const YYLTYPE *closing_loc)
{
    YSTUB("rb_node_regx_new");
    return NULL;
}

static rb_node_call_t *
rb_node_call_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc)
{
    pm_node_flags_t flags = 0;
    if (nd_recv != NULL && PM_NODE_TYPE_P(nd_recv, PM_SELF_NODE)) flags |= PM_CALL_NODE_FLAGS_IGNORE_VISIBILITY;
    return (rb_node_call_t *) pm_call_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        nd_recv, (pm_location_t) { 0 }, YID2CONST(nd_mid), (pm_location_t) { 0 },
        (pm_location_t) { 0 }, pm_yargs_from_list(p, nd_args),
        (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);
}

static rb_node_opcall_t *
rb_node_opcall_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc)
{
    return (rb_node_opcall_t *) pm_call_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        nd_recv, (pm_location_t) { 0 }, YID2CONST(nd_mid), (pm_location_t) { 0 },
        (pm_location_t) { 0 }, pm_yargs_from_list(p, nd_args),
        (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);
}

static rb_node_fcall_t *
rb_node_fcall_new(struct parser_params *p, ID nd_mid, NODE *nd_args, const YYLTYPE *loc)
{
    pm_location_t location = pm_yloc(loc);
    return (rb_node_fcall_t *) pm_call_node_new(
        p->pm->arena, ++p->pm->node_id, PM_CALL_NODE_FLAGS_IGNORE_VISIBILITY,
        location, NULL, (pm_location_t) { 0 }, YID2CONST(nd_mid), location,
        (pm_location_t) { 0 }, pm_yargs_from_list(p, nd_args),
        (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);
}

static rb_node_qcall_t *
rb_node_qcall_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc)
{
    pm_node_flags_t flags = PM_CALL_NODE_FLAGS_SAFE_NAVIGATION;
    if (nd_recv != NULL && PM_NODE_TYPE_P(nd_recv, PM_SELF_NODE)) flags |= PM_CALL_NODE_FLAGS_IGNORE_VISIBILITY;
    return (rb_node_qcall_t *) pm_call_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        nd_recv, (pm_location_t) { 0 }, YID2CONST(nd_mid), (pm_location_t) { 0 },
        (pm_location_t) { 0 }, pm_yargs_from_list(p, nd_args),
        (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);
}

static rb_node_vcall_t *
rb_node_vcall_new(struct parser_params *p, ID nd_mid, const YYLTYPE *loc)
{
    pm_location_t location = pm_yloc(loc);
    return (rb_node_vcall_t *) pm_call_node_new(
        p->pm->arena, ++p->pm->node_id,
        PM_CALL_NODE_FLAGS_VARIABLE_CALL | PM_CALL_NODE_FLAGS_IGNORE_VISIBILITY,
        location, NULL, (pm_location_t) { 0 }, YID2CONST(nd_mid), location,
        (pm_location_t) { 0 }, NULL, (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);
}

static rb_node_once_t *
rb_node_once_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc)
{
    YSTUB("rb_node_once_new");
    return NULL;
}

static rb_node_args_t *
rb_node_args_new(struct parser_params *p, const YYLTYPE *loc)
{
    YSTUB("rb_node_args_new");
    return NULL;
}

static rb_node_args_aux_t *
rb_node_args_aux_new(struct parser_params *p, ID nd_pid, int nd_plen, const YYLTYPE *loc)
{
    pm_location_t location = pm_yloc(loc);

    /* a nameless internal ID means an unported path (destructured parameters);
     * the YSTUB there already reported, so just keep the tree materializable */
    pm_constant_id_t name = pm_yid2const(p, nd_pid);
    if (name == PM_CONSTANT_ID_UNSET) return NULL;

    pm_node_t *required = (pm_node_t *) pm_required_parameter_node_new(
        p->pm->arena, ++p->pm->node_id, 0, location, name);

    pm_node_list_t elements = { 0 };
    pm_node_list_append(p->pm->arena, &elements, required);
    (void) nd_plen;
    return (rb_node_args_aux_t *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, location, elements,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_opt_arg_t *
rb_node_opt_arg_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc)
{
    if (nd_body == NULL || !PM_NODE_TYPE_P(nd_body, PM_LOCAL_VARIABLE_WRITE_NODE)) {
        YSTUB("rb_node_opt_arg_new");
        return NULL;
    }

    pm_local_variable_write_node_t *write = (pm_local_variable_write_node_t *) nd_body;

    /* the `=` between name and default, by the usual scan */
    pm_location_t operator = { 0 };
    if (write->value != NULL) {
        uint32_t scan = write->name_loc.start + write->name_loc.length;
        while (scan < write->value->location.start && p->pm->start[scan] != '=') scan++;
        if (scan < write->value->location.start) operator = (pm_location_t) { scan, 1 };
    }

    NODE *param = (NODE *) pm_optional_parameter_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        write->name, write->name_loc, operator, write->value);

    pm_node_list_t elements = { 0 };
    pm_node_list_append(p->pm->arena, &elements, param);
    return (rb_node_opt_arg_t *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, param->location, elements,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_kw_arg_t *
rb_node_kw_arg_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc)
{
    YSTUB("rb_node_kw_arg_new");
    return NULL;
}

static rb_node_postarg_t *
rb_node_postarg_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc)
{
    /* a two-slot carrier: the rest target (or the no-name marker, never
     * dereferenced) and the carrier of trailing targets */
    pm_node_list_t parts = { 0 };
    pm_node_list_append(p->pm->arena, &parts, (pm_node_t *) nd_1st);
    pm_node_list_append(p->pm->arena, &parts, (pm_node_t *) nd_2nd);
    return (rb_node_postarg_t *) pm_array_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), parts,
        (pm_location_t) { 0 }, (pm_location_t) { 0 });
}

static rb_node_argscat_t *
rb_node_argscat_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc)
{
    YSTUB("rb_node_argscat_new");
    return NULL;
}

static rb_node_argspush_t *
rb_node_argspush_new(struct parser_params *p, NODE *nd_head, NODE *nd_body, const YYLTYPE *loc)
{
    YSTUB("rb_node_argspush_new");
    return NULL;
}

static rb_node_splat_t *
rb_node_splat_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc, const YYLTYPE *operator_loc)
{
    return (rb_node_splat_t *) pm_splat_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), pm_yloc(operator_loc), nd_head);
}

static rb_node_block_pass_t *
rb_node_block_pass_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *operator_loc)
{
    return (rb_node_block_pass_t *) pm_block_argument_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), nd_body, pm_yloc(operator_loc));
}

static rb_node_alias_t *
rb_node_alias_new(struct parser_params *p, NODE *nd_1st, NODE *nd_2nd, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    return (rb_node_alias_t *) pm_alias_method_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        nd_1st, nd_2nd, pm_yloc(keyword_loc));
}

static rb_node_valias_t *
rb_node_valias_new(struct parser_params *p, ID nd_alias, ID nd_orig, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *new_loc, const YYLTYPE *old_loc)
{
    pm_node_t *new_name = (pm_node_t *) pm_global_variable_read_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(new_loc), YID2CONST(nd_alias));
    pm_node_t *old_name = (pm_node_t *) pm_global_variable_read_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(old_loc), YID2CONST(nd_orig));
    return (rb_node_valias_t *) pm_alias_global_variable_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        new_name, old_name, pm_yloc(keyword_loc));
}

static rb_node_undef_t *
rb_node_undef_new(struct parser_params *p, NODE *nd_undef, const YYLTYPE *loc)
{
    pm_node_list_t names = { 0 };
    if (nd_undef != NULL) pm_node_list_append(p->pm->arena, &names, nd_undef);
    return (rb_node_undef_t *) pm_undef_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        names, (pm_location_t) { 0 });
}

static rb_node_errinfo_t *
rb_node_errinfo_new(struct parser_params *p, const YYLTYPE *loc)
{
    YSTUB("rb_node_errinfo_new");
    return NULL;
}

static rb_node_defined_t *
rb_node_defined_new(struct parser_params *p, NODE *nd_head, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    YSTUB("rb_node_defined_new");
    return NULL;
}

static rb_node_postexe_t *
rb_node_postexe_new(struct parser_params *p, NODE *nd_body, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc)
{
    YSTUB("rb_node_postexe_new");
    return NULL;
}

static rb_node_attrasgn_t *
rb_node_attrasgn_new(struct parser_params *p, NODE *nd_recv, ID nd_mid, NODE *nd_args, const YYLTYPE *loc)
{
    if (!pm_yid_is_notop(nd_mid) && nd_mid != tASET) {
        YSTUB("rb_node_attrasgn_new");
        return NULL;
    }

    if (nd_mid == tASET) {
        /* a[i] = v: the []= call, its brackets decorated by the aryset
         * action, the value appended by node_assign. */
        pm_node_flags_t flags = PM_CALL_NODE_FLAGS_ATTRIBUTE_WRITE;
        if (nd_recv != NULL && PM_NODE_TYPE_P(nd_recv, PM_SELF_NODE)) flags |= PM_CALL_NODE_FLAGS_IGNORE_VISIBILITY;
        return (rb_node_attrasgn_t *) pm_call_node_new(
            p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
            nd_recv, (pm_location_t) { 0 }, YID2CONST(nd_mid), (pm_location_t) { 0 },
            (pm_location_t) { 0 }, pm_yargs_from_list(p, nd_args),
            (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);
    }

    pm_node_flags_t flags = PM_CALL_NODE_FLAGS_ATTRIBUTE_WRITE;
    if (nd_recv != NULL && PM_NODE_TYPE_P(nd_recv, PM_SELF_NODE)) flags |= PM_CALL_NODE_FLAGS_IGNORE_VISIBILITY;
    pm_call_node_t *call = pm_call_node_new(
        p->pm->arena, ++p->pm->node_id, flags, pm_yloc(loc),
        nd_recv, (pm_location_t) { 0 }, YID2CONST(nd_mid), (pm_location_t) { 0 },
        (pm_location_t) { 0 }, pm_yargs_from_list(p, nd_args),
        (pm_location_t) { 0 }, (pm_location_t) { 0 }, NULL);

    /* The message is the name without its trailing `=`; find it after the
     * call operator, both recoverable by the comment-skipping scan. */
    if (nd_recv != NULL) {
        uint32_t recv_end = nd_recv->location.start + nd_recv->location.length;
        pm_constant_t *writer = pm_constant_pool_id_to_constant(&p->pm->constant_pool, call->name);
        call->call_operator_loc = pm_ycall_operator_scan(p, recv_end, loc->end);
        if (call->call_operator_loc.length > 0 && writer != NULL && writer->length > 1) {
            const uint8_t *source = p->pm->start;
            uint32_t scan = call->call_operator_loc.start + call->call_operator_loc.length;
            while (scan < loc->end) {
                uint8_t c = source[scan];
                if (c == '#') { while (scan < loc->end && source[scan] != '\n') scan++; }
                else if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\\') scan++;
                else break;
            }
            call->message_loc = (pm_location_t) { scan, (uint32_t) (writer->length - 1) };
        }
    }

    return (rb_node_attrasgn_t *) call;
}

static rb_node_aryptn_t *
rb_node_aryptn_new(struct parser_params *p, NODE *pre_args, NODE *rest_arg, NODE *post_args, const YYLTYPE *loc)
{
    YSTUB("rb_node_aryptn_new");
    return NULL;
}

static rb_node_hshptn_t *
rb_node_hshptn_new(struct parser_params *p, NODE *nd_pconst, NODE *nd_pkwargs, NODE *nd_pkwrestarg, const YYLTYPE *loc)
{
    YSTUB("rb_node_hshptn_new");
    return NULL;
}

static rb_node_fndptn_t *
rb_node_fndptn_new(struct parser_params *p, NODE *pre_rest_arg, NODE *args, NODE *post_rest_arg, const YYLTYPE *loc)
{
    YSTUB("rb_node_fndptn_new");
    return NULL;
}

static rb_node_line_t *
rb_node_line_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_line_t *) pm_source_line_node_new(p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc));
}

static rb_node_file_t *
rb_node_file_new(struct parser_params *p, VALUE str, const YYLTYPE *loc)
{
    pm_string_t filepath;
    pm_string_constant_init(&filepath, (const char *) pm_string_source(&p->pm->filepath), pm_string_length(&p->pm->filepath));
    return (rb_node_file_t *) pm_source_file_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), filepath);
}

static rb_node_encoding_t *
rb_node_encoding_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_encoding_t *) pm_source_encoding_node_new(p->pm->arena, ++p->pm->node_id, PM_NODE_FLAG_STATIC_LITERAL, pm_yloc(loc));
}

static rb_node_cdecl_t *
rb_node_cdecl_new(struct parser_params *p, ID nd_vid, NODE *nd_value, NODE *nd_else, enum rb_parser_shareability shareability, const YYLTYPE *loc)
{
    if (nd_else != 0) {
        /* Scoped constant assignment: the path is the target; the operator
         * and value are filled in by node_assign. */
        if (!PM_NODE_TYPE_P(nd_else, PM_CONSTANT_PATH_NODE)) {
            YSTUB("rb_node_cdecl_new");
            return NULL;
        }
        return (NODE *) pm_constant_path_write_node_new(
            p->pm->arena, ++p->pm->node_id, 0, nd_else->location,
            (pm_constant_path_node_t *) nd_else, (pm_location_t) { 0 }, nd_value);
    }
    (void) shareability;
    pm_location_t name_loc = pm_yloc(loc);
    return (NODE *) pm_constant_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, name_loc,
        YID2CONST(nd_vid), name_loc, nd_value, (pm_location_t) { 0 });
}

static rb_node_op_cdecl_t *
rb_node_op_cdecl_new(struct parser_params *p, NODE *nd_head, NODE *nd_value, ID nd_aid, enum rb_parser_shareability shareability, const YYLTYPE *loc)
{
    YSTUB("rb_node_op_cdecl_new");
    return NULL;
}

static rb_node_error_t *
rb_node_error_new(struct parser_params *p, const YYLTYPE *loc)
{
    return (rb_node_error_t *) pm_error_recovery_node_new(p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc), NULL);
}

static rb_node_break_t *
rb_node_break_new(struct parser_params *p, NODE *nd_stts, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    NODE *node = add_block_exit(p, (NODE *) pm_break_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yargs_from_list(p, nd_stts), pm_yloc(keyword_loc)));
    return (rb_node_break_t *) node;
}

static rb_node_next_t *
rb_node_next_new(struct parser_params *p, NODE *nd_stts, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    NODE *node = add_block_exit(p, (NODE *) pm_next_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        pm_yargs_from_list(p, nd_stts), pm_yloc(keyword_loc)));
    return (rb_node_next_t *) node;
}

static rb_node_redo_t *
rb_node_redo_new(struct parser_params *p, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    YSTUB("rb_node_redo_new");
    return NULL;
}

static rb_node_def_temp_t *
rb_node_def_temp_new(struct parser_params *p, const YYLTYPE *loc)
{
    rb_node_def_temp_t *n = (rb_node_def_temp_t *) pm_arena_alloc(&p->pm->metadata_arena, sizeof(rb_node_def_temp_t), PRISM_ALIGNOF(rb_node_def_temp_t));

    n->save.numparam_save = 0;
    n->save.max_numparam = 0;
    n->save.ctxt = p->ctxt;
    n->nd_def = 0;
    n->nd_mid = 0;

    return n;
}

static rb_node_def_temp_t *
def_head_save(struct parser_params *p, rb_node_def_temp_t *n)
{
    n->save.numparam_save = numparam_push(p);
    n->save.max_numparam = p->max_numparam;
    return n;
}

static enum node_type
nodetype(NODE *node)			/* for debug */
{
    return (enum node_type) 0;
}

static int
nodeline(NODE *node)
{
    return 0;
}

static NODE*
newline_node(NODE *node)
{
    if (node) node->flags |= PM_NODE_FLAG_NEWLINE;
    return node;
}

static void
fixpos(NODE *node, NODE *orig)
{
    /* linenos are not tracked; locations are byte offsets */
}

static NODE*
block_append(struct parser_params *p, NODE *head, NODE *tail)
{
    if (head == NULL) return tail;
    if (tail == NULL) return head;

    pm_statements_node_t *statements = pm_ystatements_ensure(p, head);
    pm_node_list_append(p->pm->arena, &statements->body, tail);

    if (statements->base.location.start == 0 && statements->base.location.length == 0) {
        statements->base.location = tail->location;
    }
    else {
        uint32_t start = statements->base.location.start;
        uint32_t end = tail->location.start + tail->location.length;
        if (tail->location.start + tail->location.length > start) {
            statements->base.location.length = end - start;
        }
    }

    return (NODE *) statements;
}

/* append item to the list */
static NODE*
list_append(struct parser_params *p, NODE *list, NODE *item)
{
    if (list == NULL) {
        YYLTYPE item_loc = item ? pm_yloc_of(item) : NULL_LOC;
        return NEW_LIST(item, &item_loc);
    }
    if (!PM_NODE_TYPE_P(list, PM_ARRAY_NODE)) {
        YSTUB("list_append");
        return list;
    }

    pm_array_node_t *array = (pm_array_node_t *) list;
    pm_node_list_append(p->pm->arena, &array->elements, item);
    if (item != NULL) {
        uint32_t end = item->location.start + item->location.length;
        if (end > array->base.location.start + array->base.location.length) {
            array->base.location.length = end - array->base.location.start;
        }
    }
    return list;
}

/* concat two lists */
static NODE*
list_concat(struct parser_params *p, NODE *head, NODE *tail)
{
    if (head == NULL) return tail;
    if (tail == NULL) return head;
    if (!PM_NODE_TYPE_P(head, PM_ARRAY_NODE) || !PM_NODE_TYPE_P(tail, PM_ARRAY_NODE)) {
        YSTUB("list_concat");
        return head;
    }

    pm_array_node_t *head_array = (pm_array_node_t *) head;
    pm_array_node_t *tail_array = (pm_array_node_t *) tail;
    for (size_t i = 0; i < tail_array->elements.size; i++) {
        pm_node_list_append(p->pm->arena, &head_array->elements, tail_array->elements.nodes[i]);
    }
    uint32_t end = tail_array->base.location.start + tail_array->base.location.length;
    if (end > head_array->base.location.start + head_array->base.location.length) {
        head_array->base.location.length = end - head_array->base.location.start;
    }
    return head;
}

static int
literal_concat0(struct parser_params *p, rb_parser_string_t *head, rb_parser_string_t *tail)
{
    YSTUB("literal_concat0");
    return 0;
}

static rb_parser_string_t *
string_literal_head(struct parser_params *p, enum node_type htype, NODE *head)
{
    YSTUB("string_literal_head");
    return NULL;
}



/* concat two string literals */
static NODE *
literal_concat(struct parser_params *p, NODE *head, NODE *tail, const YYLTYPE *loc)
{
    if (head == NULL) return tail;
    if (tail == NULL) return head;

    bool head_str = PM_NODE_TYPE_P(head, PM_STRING_NODE);
    bool head_istr = PM_NODE_TYPE_P(head, PM_INTERPOLATED_STRING_NODE);
    bool tail_str = PM_NODE_TYPE_P(tail, PM_STRING_NODE);
    bool tail_embedded = PM_NODE_TYPE_P(tail, PM_EMBEDDED_STATEMENTS_NODE) || PM_NODE_TYPE_P(tail, PM_EMBEDDED_VARIABLE_NODE);

    if (!head_istr && !head_str) {
        if (PM_NODE_TYPE_P(head, PM_EMBEDDED_STATEMENTS_NODE) || PM_NODE_TYPE_P(head, PM_EMBEDDED_VARIABLE_NODE)) {
            head = pm_yistr(p, head);
            head_istr = true;
            head_str = false;
        }
        else {
            YSTUB("literal_concat");
            return head;
        }
    }

    if (!tail_str && !tail_embedded) {
        YSTUB("literal_concat");
        return head;
    }

    if (head_str) head = pm_yistr(p, head);

    pm_interpolated_string_node_t *istr = (pm_interpolated_string_node_t *) head;
    pm_node_list_append(p->pm->arena, &istr->parts, pm_yistr_part(tail));
    uint32_t end = tail->location.start + tail->location.length;
    istr->base.location.length = end - istr->base.location.start;
    return head;
}

static void
nd_copy_flag(NODE *new_node, NODE *old_node)
{
    /* becomes real with the node ports */
}

static NODE *
str2dstr(struct parser_params *p, NODE *node)
{
    YSTUB("str2dstr");
    return NULL;
}

static NODE *
str2regx(struct parser_params *p, NODE *node, int options, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *content_loc, const YYLTYPE *closing_loc)
{
    YSTUB("str2regx");
    return NULL;
}

static NODE *
evstr2dstr(struct parser_params *p, NODE *node)
{
    if (node == NULL || PM_NODE_TYPE_P(node, PM_STRING_NODE) || PM_NODE_TYPE_P(node, PM_INTERPOLATED_STRING_NODE)) return node;
    if (PM_NODE_TYPE_P(node, PM_EMBEDDED_STATEMENTS_NODE) || PM_NODE_TYPE_P(node, PM_EMBEDDED_VARIABLE_NODE)) {
        return pm_yistr(p, node);
    }
    YSTUB("evstr2dstr");
    return node;
}

static NODE *
new_evstr(struct parser_params *p, NODE *node, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc)
{
    if (node) {
        switch (PM_NODE_TYPE(node)) {
          case PM_EMBEDDED_STATEMENTS_NODE:
          case PM_EMBEDDED_VARIABLE_NODE:
            return node;
          default:
            /* CRuby flattens string bodies here as a compile-time
             * optimization; prism keeps the embedding. */
            break;
        }
    }
    return NEW_EVSTR(node, loc, opening_loc, closing_loc);
}

static NODE *
new_dstr(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    YSTUB("new_dstr");
    return NULL;
}

static NODE *
call_bin_op(struct parser_params *p, NODE *recv, ID id, NODE *arg1,
                const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    NODE *expr;
    value_expr(p, recv);
    value_expr(p, arg1);
    {
        YYLTYPE arg_loc = pm_yloc_of(arg1);
        expr = NEW_OPCALL(recv, id, NEW_LIST(arg1, &arg_loc), loc);
    }
    pm_ycall_message(expr, op_loc);
    return expr;
}

static NODE *
call_uni_op(struct parser_params *p, NODE *recv, ID id, const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    NODE *opcall;
    value_expr(p, recv);
    opcall = NEW_OPCALL(recv, id, 0, loc);
    pm_ycall_message(opcall, op_loc);
    return opcall;
}

static NODE *
new_qcall(struct parser_params* p, ID atype, NODE *recv, ID mid, NODE *args, const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    NODE *qcall = NEW_QCALL(atype, recv, mid, args, loc);
    if (qcall != NULL && PM_NODE_TYPE_P(qcall, PM_CALL_NODE)) {
        pm_call_node_t *call = (pm_call_node_t *) qcall;

        /* op_loc is the message token, except in the `a.(args)` forms, where
         * the rules pass the call operator itself; the operator's first byte
         * tells the two apart, and only a real message is recorded. */
        uint8_t first = p->pm->start[op_loc->beg];
        if (first == '.' || first == '&' || first == ':') {
            call->call_operator_loc = pm_yloc(op_loc);
        }
        else {
            call->message_loc = pm_yloc(op_loc);
            if (recv != NULL) {
                call->call_operator_loc = pm_ycall_operator_scan(p, recv->location.start + recv->location.length, op_loc->beg);
            }
        }

        pm_yparens_take(p, call);
        pm_yblock_pass_take(p, call);
    }
    return qcall;
}

static NODE*
new_command_qcall(struct parser_params* p, ID atype, NODE *recv, ID mid, NODE *args, NODE *block, const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    NODE *ret;
    if (block) block_dup_check(p, args, block);
    ret = new_qcall(p, atype, recv, mid, args, op_loc, loc);
    if (block) {
        YSTUB("new_command_qcall");
    }
    return ret;
}

static rb_locations_lambda_body_t*
new_locations_lambda_body(struct parser_params* p, NODE *node, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc)
{
    rb_locations_lambda_body_t *body = xcalloc(1, sizeof(rb_locations_lambda_body_t));
    body->node = node;
    body->opening_loc = *opening_loc;
    body->closing_loc = *closing_loc;
    return body;
}

static NODE *
command_add_block(struct parser_params*p, NODE *m, NODE *b, const YYLTYPE *loc)
{
    YSTUB("command_add_block");
    return NULL;
}

#define nd_once_body(node) (nd_type_p((node), NODE_ONCE) ? RNODE_ONCE(node)->nd_body : node)

static NODE*
last_expr_once_body(NODE *node)
{
    return node;
}

static NODE*
match_op(struct parser_params *p, NODE *node1, NODE *node2, const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    YSTUB("match_op");
    return NULL;
}

# if WARN_PAST_SCOPE
static int
past_dvar_p(struct parser_params *p, ID id)
{
    YSTUB("past_dvar_p");
    return NULL;
}
# endif

static int
numparam_nested_p(struct parser_params *p)
{
    YSTUB("numparam_nested_p");
    return 0;
}

static int
numparam_used_p(struct parser_params *p)
{
    YSTUB("numparam_used_p");
    return 0;
}

static int
it_used_p(struct parser_params *p)
{
    YSTUB("it_used_p");
    return 0;
}

static NODE*
gettable(struct parser_params *p, ID id, const YYLTYPE *loc)
{
    ID *vidp = NULL;
    NODE *node;
    switch (id) {
      case keyword_self:
        return NEW_SELF(loc);
      case keyword_nil:
        return NEW_NIL(loc);
      case keyword_true:
        return NEW_TRUE(loc);
      case keyword_false:
        return NEW_FALSE(loc);
      case keyword__FILE__:
        return NEW_FILE(0, loc);
      case keyword__LINE__:
        return NEW_LINE(loc);
      case keyword__ENCODING__:
        return NEW_ENCODING(loc);
    }
    switch (id_type(id)) {
      case ID_LOCAL:
        if (dyna_in_block(p) && dvar_defined_ref(p, id, &vidp)) {
            if (NUMPARAM_ID_P(id) && (numparam_nested_p(p) || it_used_p(p))) return 0;
            if (vidp) *vidp |= LVAR_USED;
            node = NEW_DVAR(id, loc);
            return node;
        }
        if (local_id_ref(p, id, &vidp)) {
            if (vidp) *vidp |= LVAR_USED;
            node = NEW_LVAR(id, loc);
            return node;
        }
        if (dyna_in_block(p) && NUMPARAM_ID_P(id) &&
            parser_numbered_param(p, NUMPARAM_ID_TO_IDX(id))) {
            if (numparam_nested_p(p) || it_used_p(p)) return 0;
            node = NEW_DVAR(id, loc);
            struct local_vars *local = p->lvtbl;
            if (!local->numparam.current) local->numparam.current = node;
            return node;
        }
        /* method call without arguments */
        if (dyna_in_block(p) && id == idIt && !(DVARS_TERMINAL_P(p->lvtbl->args) || DVARS_TERMINAL_P(p->lvtbl->args->prev))) {
            if (numparam_used_p(p)) return 0;
            if (p->max_numparam == ORDINAL_PARAM) {
                compile_error(p, "ordinary parameter is defined");
                return 0;
            }
            if (!p->it_id) {
                p->it_id = idItImplicit;
                vtable_add(p->lvtbl->args, p->it_id);
            }
            NODE *dvar = NEW_DVAR(p->it_id, loc);
            if (!p->lvtbl->it) p->lvtbl->it = dvar;
            return dvar;
        }
        return NEW_VCALL(id, loc);
      case ID_GLOBAL:
        return NEW_GVAR(id, loc);
      case ID_INSTANCE:
        return NEW_IVAR(id, loc);
      case ID_CONST:
        return NEW_CONST(id, loc);
      case ID_CLASS:
        return NEW_CVAR(id, loc);
    }
    compile_error(p, "identifier is not valid to get");
    return 0;
}

static rb_node_opt_arg_t *
opt_arg_append(struct parser_params *p, rb_node_opt_arg_t *opt_list, rb_node_opt_arg_t *opt)
{
    return (rb_node_opt_arg_t *) list_concat(p, (NODE *) opt_list, (NODE *) opt);
}

static rb_node_kw_arg_t *
kwd_append(struct parser_params *p, rb_node_kw_arg_t *kwlist, rb_node_kw_arg_t *kw)
{
    return (rb_node_kw_arg_t *) list_concat(p, (NODE *) kwlist, (NODE *) kw);
}

static NODE *
new_defined(struct parser_params *p, NODE *expr, const YYLTYPE *loc, const YYLTYPE *keyword_loc)
{
    pm_location_t lparen = { 0 };
    pm_location_t rparen = { 0 };

    /* defined?(x) owns its parentheses; a parenthesized single expression
     * unwraps into the node's lparen/rparen. */
    if (expr != NULL && PM_NODE_TYPE_P(expr, PM_PARENTHESES_NODE)) {
        pm_parentheses_node_t *parens = (pm_parentheses_node_t *) expr;
        if (parens->body != NULL && PM_NODE_TYPE_P(parens->body, PM_STATEMENTS_NODE)) {
            pm_statements_node_t *statements = (pm_statements_node_t *) parens->body;
            if (statements->body.size == 1) {
                lparen = parens->opening_loc;
                rparen = parens->closing_loc;
                expr = statements->body.nodes[0];
                expr->flags &= (pm_node_flags_t) ~PM_NODE_FLAG_NEWLINE;
            }
        }
    }

    return (NODE *) pm_defined_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        lparen, expr, rparen, pm_yloc(keyword_loc));
}

static NODE*
str_to_sym_node(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    YSTUB("str_to_sym_node");
    return NULL;
}

static NODE*
symbol_append(struct parser_params *p, NODE *symbols, NODE *symbol)
{
    if (symbol != NULL && PM_NODE_TYPE_P(symbol, PM_STRING_NODE)) {
        pm_string_node_t *string = (pm_string_node_t *) symbol;
        pm_node_flags_t flags = PM_NODE_FLAG_STATIC_LITERAL;
        if (pm_string_length(&string->unescaped) == 0 || pm_ystring_coderange_scan((const char *) pm_string_source(&string->unescaped), (long) pm_string_length(&string->unescaped), p->enc) == PM_YSTRING_CODERANGE_7BIT) {
            flags |= PM_SYMBOL_FLAGS_FORCED_US_ASCII_ENCODING;
        }
        symbol = (NODE *) pm_symbol_node_new(
            p->pm->arena, ++p->pm->node_id, flags, string->base.location,
            (pm_location_t) { 0 }, string->content_loc, (pm_location_t) { 0 },
            string->unescaped);
    }
    else {
        YSTUB("symbol_append");
    }
    return list_append(p, symbols, symbol);
}

static void
dregex_fragment_setenc(struct parser_params *p, rb_node_dregx_t *const dreg, int options)
{
    YSTUB("dregex_fragment_setenc");
    return;
}

static NODE *
new_regexp(struct parser_params *p, NODE *node, int options, const YYLTYPE *loc, const YYLTYPE *opening_loc, const YYLTYPE *content_loc, const YYLTYPE *closing_loc)
{
    YSTUB("new_regexp");
    return NULL;
}

static rb_node_kw_arg_t *
new_kw_arg(struct parser_params *p, NODE *k, const YYLTYPE *loc)
{
    YSTUB("new_kw_arg");
    return NULL;
}

static NODE *
new_xstring(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    YSTUB("new_xstring");
    return NULL;
}



static int nd_type_st_key_enable_p(NODE *node);

static void
check_literal_when(struct parser_params *p, NODE *arg, const YYLTYPE *loc)
{
    /* duplicate-when-literal warnings are deferred with all warnings */
}


static inline enum lex_state_e
parser_set_lex_state(struct parser_params *p, enum lex_state_e ls, int line)
{
    return p->lex.state = ls;
}

static void
flush_debug_buffer(struct parser_params *p, VALUE out, VALUE str)
{
    YSTUB("flush_debug_buffer");
    return;
}

static const char rb_parser_lex_state_names[][8] = {
    "BEG",    "END",    "ENDARG", "ENDFN",  "ARG",
    "CMDARG", "MID",    "FNAME",  "DOT",    "CLASS",
    "LABEL",  "LABELED","FITEM",
};




static void
append_bitstack_value(struct parser_params *p, stack_type stack, VALUE mesg)
{
    YSTUB("append_bitstack_value");
    return;
}










static int
assignable0(struct parser_params *p, ID id, const char **err)
{
    if (!id) return -1;
    switch (id) {
      case keyword_self:
        *err = "Can't change the value of self";
        return -1;
      case keyword_nil:
        *err = "Can't assign to nil";
        return -1;
      case keyword_true:
        *err = "Can't assign to true";
        return -1;
      case keyword_false:
        *err = "Can't assign to false";
        return -1;
      case keyword__FILE__:
        *err = "Can't assign to __FILE__";
        return -1;
      case keyword__LINE__:
        *err = "Can't assign to __LINE__";
        return -1;
      case keyword__ENCODING__:
        *err = "Can't assign to __ENCODING__";
        return -1;
    }
    switch (id_type(id)) {
      case ID_LOCAL:
        if (dyna_in_block(p)) {
            if (p->max_numparam > NO_PARAM && NUMPARAM_ID_P(id)) {
                compile_error(p, "Can't assign to numbered parameter _%d",
                              NUMPARAM_ID_TO_IDX(id));
                return -1;
            }
            if (dvar_curr(p, id)) return NODE_DASGN;
            if (dvar_defined(p, id)) return NODE_DASGN;
            if (local_id(p, id)) return NODE_LASGN;
            dyna_var(p, id);
            return NODE_DASGN;
        }
        else {
            if (!local_id(p, id)) local_var(p, id);
            return NODE_LASGN;
        }
        break;
      case ID_GLOBAL: return NODE_GASGN;
      case ID_INSTANCE: return NODE_IASGN;
      case ID_CONST:
        if (!p->ctxt.in_def) return NODE_CDECL;
        *err = "dynamic constant assignment";
        return -1;
      case ID_CLASS: return NODE_CVASGN;
      default:
        compile_error(p, "identifier is not valid to set");
    }
    return -1;
}

static NODE*
assignable(struct parser_params *p, ID id, NODE *val, const YYLTYPE *loc)
{
    const char *err = 0;
    int node_type = assignable0(p, id, &err);
    switch (node_type) {
      case NODE_DASGN: return NEW_DASGN(id, val, loc);
      case NODE_LASGN: return NEW_LASGN(id, val, loc);
      case NODE_GASGN: return NEW_GASGN(id, val, loc);
      case NODE_IASGN: return NEW_IASGN(id, val, loc);
      case NODE_CDECL: return NEW_CDECL(id, val, 0, p->ctxt.shareable_constant_value, loc);
      case NODE_CVASGN: return NEW_CVASGN(id, val, loc);
    }
    if (err) yyerror1(loc, err);
    return NEW_ERROR(loc);
}

static int
is_private_local_id(struct parser_params *p, ID name)
{
    YSTUB("is_private_local_id");
    return 0;
}

static int
shadowing_lvar_0(struct parser_params *p, ID name)
{
    if (dyna_in_block(p)) {
        if (dvar_curr(p, name)) {
            if (is_private_local_id(p, name)) return 1;
            yyerror0("duplicated argument name");
        }
        else if (dvar_defined(p, name) || local_id(p, name)) {
            vtable_add(p->lvtbl->vars, name);
            if (p->lvtbl->used) {
                vtable_add(p->lvtbl->used, (ID)p->ruby_sourceline | LVAR_USED);
            }
            return 0;
        }
    }
    else {
        if (local_id(p, name)) {
            if (is_private_local_id(p, name)) return 1;
            yyerror0("duplicated argument name");
        }
    }
    return 1;
}

static ID
shadowing_lvar(struct parser_params *p, ID name)
{
    shadowing_lvar_0(p, name);
    return name;
}

static void
new_bv(struct parser_params *p, ID name)
{
    if (!name) return;
    if (!is_local_id(name)) {
        compile_error(p, "invalid local variable - %"PRIsVALUE,
                      rb_id2str(name));
        return;
    }
    if (!shadowing_lvar_0(p, name)) return;
    dyna_var(p, name);
    ID *vidp = 0;
    if (dvar_defined_ref(p, name, &vidp)) {
        if (vidp) *vidp |= LVAR_USED;
    }
}

static void
aryset_check(struct parser_params *p, NODE *args)
{
    /* PORTME: rejects block/keyword arguments in an index assignment,
     * which cannot be built until block-pass and kwargs are ported */
}

static NODE *
aryset(struct parser_params *p, NODE *recv, NODE *idx, const YYLTYPE *loc)
{
    aryset_check(p, idx);
    return NEW_ATTRASGN(recv, tASET, idx, loc);
}

static void
block_dup_check(struct parser_params *p, NODE *node1, NODE *node2)
{
    /* PORTME: block-pass + literal block duplication check */
}

static NODE *
attrset(struct parser_params *p, NODE *recv, ID atype, ID id, const YYLTYPE *loc)
{
    NODE *node;
    id = rb_id_attrset(id);
    node = NEW_ATTRASGN(recv, id, 0, loc);
    if (CALL_Q_P(atype) && node != NULL) node->flags |= PM_CALL_NODE_FLAGS_SAFE_NAVIGATION;
    return node;
}

static VALUE
rb_backref_error(struct parser_params *p, NODE *node)
{
    YSTUB("rb_backref_error");
    return 0;
}

static NODE *
arg_append(struct parser_params *p, NODE *node1, NODE *node2, const YYLTYPE *loc)
{
    if (node1 == NULL) {
        YYLTYPE item_loc = node2 ? pm_yloc_of(node2) : *loc;
        return NEW_LIST(node2, &item_loc);
    }
    if (PM_NODE_TYPE_P(node1, PM_ARRAY_NODE)) return list_append(p, node1, node2);

    /* a single leading expression (a splat, or ret_args' unwrapping) grows
     * into a carrier holding both */
    YYLTYPE head_loc = pm_yloc_of(node1);
    NODE *list = NEW_LIST(node1, &head_loc);
    return list_append(p, list, node2);
}

static NODE *
arg_concat(struct parser_params *p, NODE *node1, NODE *node2, const YYLTYPE *loc)
{
    YSTUB("arg_concat");
    return NULL;
}

static NODE *
last_arg_append(struct parser_params *p, NODE *args, NODE *last_arg, const YYLTYPE *loc)
{
    NODE *n1;
    if ((n1 = splat_array(args)) != 0) {
        return list_append(p, n1, last_arg);
    }
    return arg_append(p, args, last_arg, loc);
}

static NODE *
rest_arg_append(struct parser_params *p, NODE *args, NODE *rest_arg, const YYLTYPE *loc)
{
    if (rest_arg == NULL) {
        YSTUB("rest_arg_append");
        return args;
    }

    /* the args rules pass the whole SplatNode; the mrhs form passes the bare
     * value, with the star just before it */
    if (!PM_NODE_TYPE_P(rest_arg, PM_SPLAT_NODE)) {
        uint32_t scan = rest_arg->location.start;
        while (scan > 0 && p->pm->start[scan - 1] != '*') scan--;
        pm_location_t star = { 0 };
        if (scan > 0) star = (pm_location_t) { scan - 1, 1 };

        pm_location_t splat_loc = star;
        splat_loc.length = (rest_arg->location.start + rest_arg->location.length) - splat_loc.start;
        rest_arg = (NODE *) pm_splat_node_new(
            p->pm->arena, ++p->pm->node_id, 0, splat_loc, star, rest_arg);
    }
    return arg_append(p, args, rest_arg, loc);
}

static NODE *
splat_array(NODE* node)
{
    if (node != NULL && PM_NODE_TYPE_P(node, PM_ARRAY_NODE)) return node;
    return NULL;
}

static void
mark_lvar_used(struct parser_params *p, NODE *rhs)
{
    YSTUB("mark_lvar_used");
    return;
}

static int is_static_content(NODE *node);

static NODE *
node_assign(struct parser_params *p, NODE *lhs, NODE *rhs, struct lex_context ctxt, const YYLTYPE *loc)
{
    if (!lhs) return 0;
    (void) ctxt;

    /*
     * The operator's own location: CRuby's nodes never store it, so the rules
     * do not pass it down. It is recoverable exactly: the first `=` after the
     * target is necessarily the operator, since a newline or comment before
     * it would have ended the statement.
     */
    pm_location_t operator_loc = { 0 };
    if (rhs != NULL) {
        uint32_t scan = lhs->location.start + lhs->location.length;
        while (scan < rhs->location.start && p->pm->start[scan] != '=') scan++;
        if (scan < rhs->location.start) operator_loc = (pm_location_t) { scan, 1 };
    }

    /* an mrhs value: a lone splat becomes a one-element array, and a
     * bracketless list picks up its flags (a bracketed literal is untouched) */
    if (rhs != NULL && PM_NODE_TYPE_P(rhs, PM_SPLAT_NODE)) {
        pm_node_list_t elements = { 0 };
        pm_node_list_append(p->pm->arena, &elements, rhs);
        rhs = (NODE *) pm_array_node_new(
            p->pm->arena, ++p->pm->node_id, PM_ARRAY_NODE_FLAGS_CONTAINS_SPLAT,
            rhs->location, elements, (pm_location_t) { 0 }, (pm_location_t) { 0 });
    }
    else {
        rhs = pm_yarray_finalize(p, rhs);
    }

    switch (PM_NODE_TYPE(lhs)) {
      case PM_LOCAL_VARIABLE_WRITE_NODE:
        ((pm_local_variable_write_node_t *) lhs)->operator_loc = operator_loc;
        goto assign;
      case PM_GLOBAL_VARIABLE_WRITE_NODE:
        ((pm_global_variable_write_node_t *) lhs)->operator_loc = operator_loc;
        goto assign;
      case PM_INSTANCE_VARIABLE_WRITE_NODE:
        ((pm_instance_variable_write_node_t *) lhs)->operator_loc = operator_loc;
        goto assign;
      case PM_CLASS_VARIABLE_WRITE_NODE:
        ((pm_class_variable_write_node_t *) lhs)->operator_loc = operator_loc;
        goto assign;
      case PM_CONSTANT_WRITE_NODE:
        ((pm_constant_write_node_t *) lhs)->operator_loc = operator_loc;
        goto assign;
      case PM_CONSTANT_PATH_WRITE_NODE:
        ((pm_constant_path_write_node_t *) lhs)->operator_loc = operator_loc;
        goto assign;
      case PM_MULTI_TARGET_NODE: {
        pm_multi_target_node_t *target = (pm_multi_target_node_t *) lhs;
        return (NODE *) pm_multi_write_node_new(
            p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
            target->lefts, target->rest, target->rights,
            target->lparen_loc, target->rparen_loc, operator_loc, rhs);
      }
      assign:
        set_nd_value(p, lhs, rhs);
        lhs->location = pm_yloc(loc);
        break;

      case PM_ERROR_RECOVERY_NODE:
        break;

      case PM_CALL_NODE:
        if (PM_NODE_FLAG_P(lhs, PM_CALL_NODE_FLAGS_ATTRIBUTE_WRITE)) {
            pm_call_node_t *call = (pm_call_node_t *) lhs;
            if (rhs != NULL) {
                if (call->arguments != NULL) {
                    /* index writes: the value joins the indices */
                    pm_node_list_append(p->pm->arena, &call->arguments->arguments, rhs);
                    uint32_t end = rhs->location.start + rhs->location.length;
                    call->arguments->base.location.length = end - call->arguments->base.location.start;
                }
                else {
                    pm_node_list_t arguments = { 0 };
                    pm_node_list_append(p->pm->arena, &arguments, rhs);
                    call->arguments = pm_arguments_node_new(
                        p->pm->arena, ++p->pm->node_id, 0, rhs->location, arguments);
                }
                call->equal_loc = operator_loc;
            }
            lhs->location = pm_yloc(loc);
            break;
        }
        YSTUB("node_assign");
        break;

      default:
        YSTUB("node_assign");
        break;
    }

    return lhs;
}

static NODE *
value_expr_check(struct parser_params *p, NODE *node)
{
    return NULL; /* not void */
}

static int
value_expr(struct parser_params *p, NODE *node)
{
    return TRUE;
}

static void
void_expr(struct parser_params *p, NODE *node)
{
    /* void-expression warnings are not ported */
}

/* warns useless use of block and returns the last statement node */
static NODE *
void_stmts(struct parser_params *p, NODE *node)
{
    return node;
}

static NODE *
remove_begin(NODE *node)
{
    return node;
}

static void
reduce_nodes(struct parser_params *p, NODE **body)
{
    YSTUB("reduce_nodes");
    return;
}

static int
is_static_content(NODE *node)
{
    return 0;
}

static int
assign_in_cond(struct parser_params *p, NODE *node)
{
    YSTUB("assign_in_cond");
    return 0;
}

enum cond_type {
    COND_IN_OP,
    COND_IN_COND,
    COND_IN_FF
};

#define SWITCH_BY_COND_TYPE(t, w, arg) do { \
    switch (t) { \
      case COND_IN_OP: break; \
      case COND_IN_COND: rb_##w##0(arg "literal in condition"); break; \
      case COND_IN_FF: rb_##w##0(arg "literal in flip-flop"); break; \
    } \
} while (0)

static NODE *cond0(struct parser_params*,NODE*,enum cond_type,const YYLTYPE*,bool);

static NODE*
range_op(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    YSTUB("range_op");
    return NULL;
}

static NODE*
cond0(struct parser_params *p, NODE *node, enum cond_type type, const YYLTYPE *loc, bool top)
{
    YSTUB("cond0");
    return NULL;
}

static NODE*
cond(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    if (node == 0) return 0;
    /* PORTME: as method_cond. */
    return node;
}

static NODE*
method_cond(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    if (node == 0) return 0;
    /* PORTME: cond0's regexp/range/flip-flop condition rewrites arrive with
     * those nodes; every other expression passes through unchanged. */
    return node;
}

static NODE*
new_nil_at(struct parser_params *p, const rb_code_position_t *pos)
{
    /* prism's open-ended ranges have no node on the open side. */
    (void) pos;
    return NULL;
}

static NODE*
new_if(struct parser_params *p, NODE *cc, NODE *left, NODE *right, const YYLTYPE *loc, const YYLTYPE* if_keyword_loc, const YYLTYPE* then_keyword_loc, const YYLTYPE* end_keyword_loc)
{
    if (!cc) return right;
    cc = cond(p, cc, loc);
    return newline_node(NEW_IF(cc, left, right, loc, if_keyword_loc, then_keyword_loc, end_keyword_loc));
}

static NODE*
new_unless(struct parser_params *p, NODE *cc, NODE *left, NODE *right, const YYLTYPE *loc, const YYLTYPE *keyword_loc, const YYLTYPE *then_keyword_loc, const YYLTYPE *end_keyword_loc)
{
    if (!cc) return right;
    cc = cond(p, cc, loc);
    return newline_node(NEW_UNLESS(cc, left, right, loc, keyword_loc, then_keyword_loc, end_keyword_loc));
}

#define NEW_AND_OR(type, f, s, loc, op_loc) (type == NODE_AND ? NEW_AND(f,s,loc,op_loc) : NEW_OR(f,s,loc,op_loc))

static NODE*
logop(struct parser_params *p, ID id, NODE *left, NODE *right,
          const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    bool is_and = (id == idAND || id == idANDOP);
    value_expr(p, left);

    /* CRuby rebuilds `a and b and c` to nest rightward for its compiler;
     * prism keeps the grammar's left association, so no rebuild here. */
    return is_and ? (NODE *) NEW_AND(left, right, loc, op_loc) : (NODE *) NEW_OR(left, right, loc, op_loc);
}

#undef NEW_AND_OR

static void
no_blockarg(struct parser_params *p, NODE *node)
{
    (void) node;
    if (p->yblock_pass != NULL) {
        p->yblock_pass = NULL;
        compile_error(p, "block argument should not be given");
    }
}

static NODE *
ret_args(struct parser_params *p, NODE *node)
{
    if (node) {
        no_blockarg(p, node);
        if (PM_NODE_TYPE_P(node, PM_ARRAY_NODE) && ((pm_array_node_t *) node)->elements.size == 1) {
            node = ((pm_array_node_t *) node)->elements.nodes[0];
        }
    }
    return node;
}

static NODE*
negate_lit(struct parser_params *p, NODE* node, const YYLTYPE *loc)
{
    switch (PM_NODE_TYPE(node)) {
      case PM_INTEGER_NODE:
        ((pm_integer_node_t *) node)->value.negative = true;
        break;
      case PM_FLOAT_NODE:
        ((pm_float_node_t *) node)->value = -((pm_float_node_t *) node)->value;
        break;
      case PM_RATIONAL_NODE:
        ((pm_rational_node_t *) node)->numerator.negative = true;
        break;
      case PM_IMAGINARY_NODE: {
        /* the sign lives on the numeric child; both spans grow to cover it */
        YYLTYPE numeric_loc = *loc;
        numeric_loc.end -= 1;
        negate_lit(p, ((pm_imaginary_node_t *) node)->numeric, &numeric_loc);
        break;
      }
      default:
        YSTUB("negate_lit");
        break;
    }
    node->location = pm_yloc(loc);
    return node;
}

static NODE *
arg_blk_pass(struct parser_params *p, NODE *node1, rb_node_block_pass_t *node2)
{
    if (node2) p->yblock_pass = (NODE *) node2;
    return node1;
}

static bool
args_info_empty_p(struct rb_args_info *args)
{
    return 1;
}

static rb_node_args_t *
new_args(struct parser_params *p, rb_node_args_aux_t *pre_args, rb_node_opt_arg_t *opt_args, ID rest_arg, rb_node_args_aux_t *post_args, rb_node_args_t *tail, const YYLTYPE *loc)
{
    if (pre_args == NULL && opt_args == NULL && rest_arg == 0 && post_args == NULL && tail == NULL) return NULL;

    pm_node_list_t requireds = { 0 };
    pm_node_list_t optionals = { 0 };
    pm_node_list_t posts = { 0 };
    pm_node_t *rest = NULL;

    if (pre_args != NULL) {
        if (PM_NODE_TYPE_P((NODE *) pre_args, PM_ARRAY_NODE)) requireds = ((pm_array_node_t *) pre_args)->elements;
        else { YSTUB("new_args"); }
    }
    if (opt_args != NULL) {
        if (PM_NODE_TYPE_P((NODE *) opt_args, PM_ARRAY_NODE)) optionals = ((pm_array_node_t *) opt_args)->elements;
        else { YSTUB("new_args"); }
    }
    if (post_args != NULL) {
        if (PM_NODE_TYPE_P((NODE *) post_args, PM_ARRAY_NODE)) posts = ((pm_array_node_t *) post_args)->elements;
        else { YSTUB("new_args"); }
    }
    if (rest_arg != 0) {
        rest = p->yrest_param;
        p->yrest_param = NULL;
    }

    pm_parameters_node_t *parameters;
    if (tail != NULL && PM_NODE_TYPE_P((NODE *) tail, PM_PARAMETERS_NODE)) {
        parameters = (pm_parameters_node_t *) tail;
    }
    else {
        if (tail != NULL) YSTUB("new_args");
        parameters = pm_parameters_node_new(
            p->pm->arena, ++p->pm->node_id, 0, (pm_location_t) { 0 },
            (pm_node_list_t) { 0 }, (pm_node_list_t) { 0 }, NULL,
            (pm_node_list_t) { 0 }, (pm_node_list_t) { 0 }, NULL, NULL);
    }

    parameters->requireds = requireds;
    parameters->optionals = optionals;
    parameters->rest = rest;
    parameters->posts = posts;
    parameters->base.location = pm_yloc(loc);
    return (rb_node_args_t *) parameters;
}

static rb_node_args_t *
new_args_tail(struct parser_params *p, rb_node_kw_arg_t *kw_args, ID kw_rest_arg, ID block, const YYLTYPE *kw_rest_loc)
{
    if (kw_args == NULL && kw_rest_arg == 0 && block == 0) return NULL;
    (void) kw_rest_loc;

    pm_node_list_t keywords = { 0 };
    if (kw_args != NULL && PM_NODE_TYPE_P((NODE *) kw_args, PM_ARRAY_NODE)) {
        keywords = ((pm_array_node_t *) kw_args)->elements;
    }
    else if (kw_args != NULL) {
        YSTUB("new_args_tail");
    }

    pm_node_t *keyword_rest = NULL;
    if (kw_rest_arg != 0) {
        keyword_rest = p->ykwrest_param;
        p->ykwrest_param = NULL;
    }

    pm_node_t *block_param = NULL;
    if (block != 0) {
        block_param = p->yblock_param;
        p->yblock_param = NULL;
        if (block == idNil) YSTUB("new_args_tail &nil");
    }

    return (rb_node_args_t *) pm_parameters_node_new(
        p->pm->arena, ++p->pm->node_id, 0, (pm_location_t) { 0 },
        (pm_node_list_t) { 0 }, (pm_node_list_t) { 0 }, NULL,
        (pm_node_list_t) { 0 }, keywords, keyword_rest, (pm_node_t *) block_param);
}

static rb_node_args_t *
args_with_numbered(struct parser_params *p, rb_node_args_t *args, int max_numparam, ID it_id)
{
    if (max_numparam <= 0 && it_id == 0) return args;
    YSTUB("args_with_numbered"); /* PORTME: numbered parameters and it */
    return args;
}

static NODE*
new_array_pattern(struct parser_params *p, NODE *constant, NODE *pre_arg, NODE *aryptn, const YYLTYPE *loc)
{
    YSTUB("new_array_pattern");
    return NULL;
}

static NODE*
new_array_pattern_tail(struct parser_params *p, NODE *pre_args, int has_rest, NODE *rest_arg, NODE *post_args, const YYLTYPE *loc)
{
    YSTUB("new_array_pattern_tail");
    return NULL;
}

static NODE*
new_find_pattern(struct parser_params *p, NODE *constant, NODE *fndptn, const YYLTYPE *loc)
{
    YSTUB("new_find_pattern");
    return NULL;
}

static NODE*
new_find_pattern_tail(struct parser_params *p, NODE *pre_rest_arg, NODE *args, NODE *post_rest_arg, const YYLTYPE *loc)
{
    YSTUB("new_find_pattern_tail");
    return NULL;
}

static NODE*
new_hash_pattern(struct parser_params *p, NODE *constant, NODE *hshptn, const YYLTYPE *loc)
{
    YSTUB("new_hash_pattern");
    return NULL;
}

static NODE*
new_hash_pattern_tail(struct parser_params *p, NODE *kw_args, ID kw_rest_arg, const YYLTYPE *loc)
{
    YSTUB("new_hash_pattern_tail");
    return NULL;
}

static NODE*
dsym_node(struct parser_params *p, NODE *node, const YYLTYPE *loc)
{
    YSTUB("dsym_node");
    return NULL;
}

static int
nd_type_st_key_enable_p(NODE *node)
{
    return 0;
}

static VALUE
nd_value(struct parser_params *p, NODE *node)
{
    YSTUB("nd_value");
    return 0;
}

static void
warn_duplicate_keys(struct parser_params *p, NODE *hash)
{
    YSTUB("warn_duplicate_keys");
    return;
}

static NODE *
new_hash(struct parser_params *p, NODE *hash, const YYLTYPE *loc)
{
    pm_node_list_t elements = { 0 };
    pm_location_t location = pm_yloc(loc);

    if (hash != NULL) {
        if (!PM_NODE_TYPE_P(hash, PM_ARRAY_NODE)) {
            YSTUB("new_hash");
            return NULL;
        }
        elements = ((pm_array_node_t *) hash)->elements;
        location = hash->location;
    }

    /* the keyword form is what argument lists want; the braced hash literal
     * re-expresses it in pm_yhash_braces */
    pm_node_flags_t flags = PM_KEYWORD_HASH_NODE_FLAGS_SYMBOL_KEYS;
    for (size_t i = 0; i < elements.size; i++) {
        pm_node_t *element = elements.nodes[i];
        if (!PM_NODE_TYPE_P(element, PM_ASSOC_NODE) ||
            ((pm_assoc_node_t *) element)->key == NULL ||
            !PM_NODE_TYPE_P(((pm_assoc_node_t *) element)->key, PM_SYMBOL_NODE)) {
            flags = 0;
            break;
        }
    }

    return (NODE *) pm_keyword_hash_node_new(
        p->pm->arena, ++p->pm->node_id, flags, location, elements);
}

static void
error_duplicate_pattern_variable(struct parser_params *p, ID id, const YYLTYPE *loc)
{
    YSTUB("error_duplicate_pattern_variable");
    return;
}

static void
error_duplicate_pattern_key(struct parser_params *p, ID key, const YYLTYPE *loc)
{
    YSTUB("error_duplicate_pattern_key");
    return;
}

static NODE *
new_unique_key_hash(struct parser_params *p, NODE *hash, const YYLTYPE *loc)
{
    YSTUB("new_unique_key_hash");
    return NULL;
}

static NODE *
new_op_assign(struct parser_params *p, NODE *lhs, ID op, NODE *rhs, struct lex_context ctxt, const YYLTYPE *op_loc, const YYLTYPE *loc)
{
    (void) ctxt;
    if (lhs == NULL) return NULL;

    pm_location_t location = pm_yloc(loc);
    pm_location_t operator = pm_yloc(op_loc);
    bool is_or = (op == idOROP);
    bool is_and = (op == idANDOP);
    pm_constant_id_t binop = (is_or || is_and) ? 0 : YID2CONST(op);

#define YOPW(prefix, name_expr, name_loc_expr, depth_args) \
    (is_or ? (NODE *) prefix##_or_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, name_expr, name_loc_expr, operator, rhs depth_args) : \
     is_and ? (NODE *) prefix##_and_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, name_expr, name_loc_expr, operator, rhs depth_args) : \
     (NODE *) prefix##_operator_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, name_expr, name_loc_expr, operator, rhs, binop depth_args))

    switch (PM_NODE_TYPE(lhs)) {
      case PM_LOCAL_VARIABLE_WRITE_NODE: {
        pm_local_variable_write_node_t *write = (pm_local_variable_write_node_t *) lhs;
        /* locals order name_loc/operator/value differently and carry depth */
        if (is_or) return (NODE *) pm_local_variable_or_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, write->name_loc, operator, rhs, write->name, write->depth);
        if (is_and) return (NODE *) pm_local_variable_and_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, write->name_loc, operator, rhs, write->name, write->depth);
        return (NODE *) pm_local_variable_operator_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, write->name_loc, operator, rhs, write->name, binop, write->depth);
      }
      case PM_INSTANCE_VARIABLE_WRITE_NODE: {
        pm_instance_variable_write_node_t *write = (pm_instance_variable_write_node_t *) lhs;
        return YOPW(pm_instance_variable, write->name, write->name_loc, );
      }
      case PM_GLOBAL_VARIABLE_WRITE_NODE: {
        pm_global_variable_write_node_t *write = (pm_global_variable_write_node_t *) lhs;
        return YOPW(pm_global_variable, write->name, write->name_loc, );
      }
      case PM_CLASS_VARIABLE_WRITE_NODE: {
        pm_class_variable_write_node_t *write = (pm_class_variable_write_node_t *) lhs;
        return YOPW(pm_class_variable, write->name, write->name_loc, );
      }
      case PM_CONSTANT_WRITE_NODE: {
        pm_constant_write_node_t *write = (pm_constant_write_node_t *) lhs;
        return YOPW(pm_constant, write->name, write->name_loc, );
      }
      default:
        YSTUB("new_op_assign");
        return lhs;
    }
#undef YOPW
}

static NODE *
new_ary_op_assign(struct parser_params *p, NODE *ary,
                  NODE *args, ID op, NODE *rhs, const YYLTYPE *args_loc, const YYLTYPE *loc,
                  const YYLTYPE *call_operator_loc, const YYLTYPE *opening_loc, const YYLTYPE *closing_loc, const YYLTYPE *binary_operator_loc)
{
    pm_location_t location = pm_yloc(loc);
    pm_location_t operator = pm_yloc(binary_operator_loc);
    pm_arguments_node_t *arguments = pm_yargs_from_list(p, args);
    (void) args_loc;
    (void) call_operator_loc;

    if (op == idOROP) {
        return (NODE *) pm_index_or_write_node_new(
            p->pm->arena, ++p->pm->node_id, 0, location, ary, (pm_location_t) { 0 },
            pm_yloc(opening_loc), arguments, pm_yloc(closing_loc), NULL, operator, rhs);
    }
    if (op == idANDOP) {
        return (NODE *) pm_index_and_write_node_new(
            p->pm->arena, ++p->pm->node_id, 0, location, ary, (pm_location_t) { 0 },
            pm_yloc(opening_loc), arguments, pm_yloc(closing_loc), NULL, operator, rhs);
    }
    return (NODE *) pm_index_operator_write_node_new(
        p->pm->arena, ++p->pm->node_id, 0, location, ary, (pm_location_t) { 0 },
        pm_yloc(opening_loc), arguments, pm_yloc(closing_loc), NULL,
        YID2CONST(op), operator, rhs);
}

static NODE *
new_attr_op_assign(struct parser_params *p, NODE *lhs,
                   ID atype, ID attr, ID op, NODE *rhs, const YYLTYPE *loc,
                   const YYLTYPE *call_operator_loc, const YYLTYPE *message_loc, const YYLTYPE *binary_operator_loc)
{
    pm_location_t location = pm_yloc(loc);
    pm_location_t operator = pm_yloc(binary_operator_loc);
    pm_location_t call_operator = pm_yloc(call_operator_loc);
    pm_location_t message = pm_yloc(message_loc);
    pm_constant_id_t read_name = YID2CONST(attr);
    pm_constant_id_t write_name = YID2CONST(pm_yid_attrset(&p->pm->metadata_arena, &p->pm->constant_pool, attr));
    pm_node_flags_t flags = CALL_Q_P(atype) ? PM_CALL_NODE_FLAGS_SAFE_NAVIGATION : 0;

    if (op == idOROP) {
        return (NODE *) pm_call_or_write_node_new(
            p->pm->arena, ++p->pm->node_id, flags, location, lhs, call_operator, message,
            read_name, write_name, operator, rhs);
    }
    if (op == idANDOP) {
        return (NODE *) pm_call_and_write_node_new(
            p->pm->arena, ++p->pm->node_id, flags, location, lhs, call_operator, message,
            read_name, write_name, operator, rhs);
    }
    return (NODE *) pm_call_operator_write_node_new(
        p->pm->arena, ++p->pm->node_id, flags, location, lhs, call_operator, message,
        read_name, write_name, YID2CONST(op), operator, rhs);
}

static NODE *
new_const_op_assign(struct parser_params *p, NODE *lhs, ID op, NODE *rhs, struct lex_context ctxt, const YYLTYPE *loc)
{
    (void) ctxt;
    pm_location_t location = pm_yloc(loc);

    if (lhs == NULL || !PM_NODE_TYPE_P(lhs, PM_CONSTANT_PATH_NODE)) {
        YSTUB("new_const_op_assign");
        return lhs;
    }

    /* the operator sits between the path and the value */
    pm_location_t operator = { 0 };
    {
        uint32_t scan = lhs->location.start + lhs->location.length;
        const uint8_t *source = p->pm->start;
        while (rhs != NULL && scan < rhs->location.start) {
            uint8_t c = source[scan];
            if (c == '#') { while (scan < rhs->location.start && source[scan] != '\n') scan++; }
            else if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\\') scan++;
            else break;
        }
        if (rhs != NULL && scan < rhs->location.start) {
            uint32_t end = scan;
            while (end < rhs->location.start && source[end] != ' ' && source[end] != '\t' && source[end] != '\n') end++;
            operator = (pm_location_t) { scan, end - scan };
        }
    }

    pm_constant_path_node_t *target = (pm_constant_path_node_t *) lhs;
    if (op == idOROP) {
        return (NODE *) pm_constant_path_or_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, target, operator, rhs);
    }
    if (op == idANDOP) {
        return (NODE *) pm_constant_path_and_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, target, operator, rhs);
    }
    return (NODE *) pm_constant_path_operator_write_node_new(p->pm->arena, ++p->pm->node_id, 0, location, target, operator, rhs, YID2CONST(op));
}

static NODE *
const_decl(struct parser_params *p, NODE *path, const YYLTYPE *loc)
{
    if (p->ctxt.in_def) {
        yyerror1(loc, "dynamic constant assignment");
    }
    return NEW_CDECL(0, 0, (path), p->ctxt.shareable_constant_value, loc);
}


static NODE *
new_bodystmt(struct parser_params *p, NODE *head, NODE *rescue, NODE *rescue_else, NODE *ensure, const YYLTYPE *loc)
{
    if (rescue == NULL && rescue_else == NULL && ensure == NULL) return head;

    pm_ensure_node_t *ensure_clause = (ensure != NULL && PM_NODE_TYPE_P(ensure, PM_ENSURE_NODE)) ? (pm_ensure_node_t *) ensure : NULL;
    pm_else_node_t *else_clause = (rescue_else != NULL && PM_NODE_TYPE_P(rescue_else, PM_ELSE_NODE)) ? (pm_else_node_t *) rescue_else : NULL;
    pm_rescue_node_t *rescue_clause = (rescue != NULL && PM_NODE_TYPE_P(rescue, PM_RESCUE_NODE)) ? (pm_rescue_node_t *) rescue : NULL;

    if ((rescue != NULL && rescue_clause == NULL) || (rescue_else != NULL && else_clause == NULL) || (ensure != NULL && ensure_clause == NULL)) {
        YSTUB("new_bodystmt");
    }

    /* An else clause's span runs to the next keyword, known here if it is
     * ensure and stamped later if it is the closing end. */
    if (else_clause != NULL && ensure_clause != NULL) {
        pm_location_t next_keyword = ensure_clause->ensure_keyword_loc;
        else_clause->end_keyword_loc = next_keyword;
        else_clause->base.location.length = (next_keyword.start + next_keyword.length) - else_clause->base.location.start;
    }

    return (NODE *) pm_begin_node_new(
        p->pm->arena, ++p->pm->node_id, 0, pm_yloc(loc),
        (pm_location_t) { 0 }, pm_ystatements_opt(p, head),
        rescue_clause, else_clause, ensure_clause, (pm_location_t) { 0 });
}

static void
warn_unused_var(struct parser_params *p, struct local_vars *local)
{
    YSTUB("warn_unused_var");
    return;
}

static void
local_push(struct parser_params *p, int toplevel_scope)
{
    struct local_vars *local;
    int inherits_dvars = toplevel_scope && compile_for_eval;
    int warn_unused_vars = RTEST(ruby_verbose);

    local = ALLOC(struct local_vars);
    local->prev = p->lvtbl;
    local->args = vtable_alloc(0);
    local->vars = vtable_alloc(inherits_dvars ? DVARS_INHERIT : DVARS_TOPSCOPE);
    if (toplevel_scope && compile_for_eval) warn_unused_vars = 0;
    if (toplevel_scope && e_option_supplied(p)) warn_unused_vars = 0;
    local->numparam.outer = 0;
    local->numparam.inner = 0;
    local->numparam.current = 0;
    local->it = 0;
    local->used = warn_unused_vars ? vtable_alloc(0) : 0;

# if WARN_PAST_SCOPE
    local->past = 0;
# endif
    CMDARG_PUSH(0);
    COND_PUSH(0);
    p->lvtbl = local;
}

static void
vtable_chain_free(struct parser_params *p, struct vtable *table)
{
    while (!DVARS_TERMINAL_P(table)) {
        struct vtable *cur_table = table;
        table = cur_table->prev;
        vtable_free(cur_table);
    }
}

static void
local_free(struct parser_params *p, struct local_vars *local)
{
    vtable_chain_free(p, local->used);

# if WARN_PAST_SCOPE
    vtable_chain_free(p, local->past);
# endif

    vtable_chain_free(p, local->args);
    vtable_chain_free(p, local->vars);

    ruby_xfree_sized(local, sizeof(struct local_vars));
}

static void
local_pop(struct parser_params *p)
{
    struct local_vars *local = p->lvtbl->prev;
    if (p->lvtbl->used) {
        warn_unused_var(p, p->lvtbl);
    }

    local_free(p, p->lvtbl);
    p->lvtbl = local;

    CMDARG_POP();
    COND_POP();
}

static rb_ast_id_table_t *
local_tbl(struct parser_params *p)
{
    int cnt_args = vtable_size(p->lvtbl->args);
    int cnt_vars = vtable_size(p->lvtbl->vars);
    int cnt = cnt_args + cnt_vars;
    int i, j;
    rb_ast_id_table_t *tbl;

    if (cnt <= 0) return 0;
    tbl = xmalloc(sizeof(rb_ast_id_table_t) + (size_t) cnt * sizeof(ID));
    tbl->size = cnt;
    MEMCPY(tbl->ids, p->lvtbl->args->tbl, ID, cnt_args);
    /* remove IDs duplicated to warn shadowing */
    for (i = 0, j = cnt_args; i < cnt_vars; ++i) {
        ID id = p->lvtbl->vars->tbl[i];
        if (!vtable_included(p->lvtbl->args, id)) {
            tbl->ids[j++] = id;
        }
    }
    if (j < cnt) {
        tbl->size = j;
    }

    return tbl;
}

static void
numparam_name(struct parser_params *p, ID id)
{
    if (!NUMPARAM_ID_P(id)) return;
    compile_error(p, "_%d is reserved for numbered parameter",
        NUMPARAM_ID_TO_IDX(id));
}

static void
arg_var(struct parser_params *p, ID id)
{
    numparam_name(p, id);
    vtable_add(p->lvtbl->args, id);
}

static void
local_var(struct parser_params *p, ID id)
{
    numparam_name(p, id);
    vtable_add(p->lvtbl->vars, id);
    if (p->lvtbl->used) {
        vtable_add(p->lvtbl->used, (ID)p->ruby_sourceline);
    }
}

static int
rb_parser_local_defined(struct parser_params *p, ID id, const struct rb_iseq_struct *iseq)
{
    /* PORTME: outer eval scopes arrive with the scopes option */
    return 0;
}

static int
local_id_ref(struct parser_params *p, ID id, ID **vidrefp)
{
    struct vtable *vars, *args, *used;

    vars = p->lvtbl->vars;
    args = p->lvtbl->args;
    used = p->lvtbl->used;

    while (vars && !DVARS_TERMINAL_P(vars->prev)) {
        vars = vars->prev;
        args = args->prev;
        if (used) used = used->prev;
    }

    if (vars && vars->prev == DVARS_INHERIT) {
        return 0; /* PORTME: outer eval scopes arrive with the scopes option */
    }
    else if (vtable_included(args, id)) {
        return 1;
    }
    else {
        int i = vtable_included(vars, id);
        if (i && used && vidrefp) *vidrefp = &used->tbl[i-1];
        return i != 0;
    }
}

static int
local_id(struct parser_params *p, ID id)
{
    return local_id_ref(p, id, NULL);
}

static int
check_forwarding_args(struct parser_params *p)
{
    YSTUB("check_forwarding_args");
    return 0;
}

static void
add_forwarding_args(struct parser_params *p)
{
    YSTUB("add_forwarding_args");
    return;
}

static void
forwarding_arg_check(struct parser_params *p, ID arg, ID all, const char *var)
{
    bool conflict = false;

    struct vtable *vars, *args;

    vars = p->lvtbl->vars;
    args = p->lvtbl->args;

    while (vars && !DVARS_TERMINAL_P(vars->prev)) {
        conflict |= (vtable_included(args, arg) && !(all && vtable_included(args, all)));
        vars = vars->prev;
        args = args->prev;
    }

    bool found = false;
    if (vars && vars->prev == DVARS_INHERIT && !found) {
        found = 0; /* PORTME: outer eval scopes arrive with the scopes option */
    }
    else {
        found = (vtable_included(args, arg) &&
                 !(all && vtable_included(args, all)));
    }

    if (!found) {
        compile_error(p, "no anonymous %s parameter", var);
    }
    else if (conflict) {
        compile_error(p, "anonymous %s parameter is also used within block", var);
    }
}

static NODE *
new_args_forward_call(struct parser_params *p, NODE *leading, const YYLTYPE *loc, const YYLTYPE *argsloc)
{
    YSTUB("new_args_forward_call");
    return NULL;
}

static NODE *
numparam_push(struct parser_params *p)
{
    struct local_vars *local = p->lvtbl;
    NODE *inner = local->numparam.inner;
    if (!local->numparam.outer) {
        local->numparam.outer = local->numparam.current;
    }
    local->numparam.inner = 0;
    local->numparam.current = 0;
    local->it = 0;
    return inner;
}

static void
numparam_pop(struct parser_params *p, NODE *prev_inner)
{
    struct local_vars *local = p->lvtbl;
    if (prev_inner) {
        /* prefer first one */
        local->numparam.inner = prev_inner;
    }
    else if (local->numparam.current) {
        /* current and inner are exclusive */
        local->numparam.inner = local->numparam.current;
    }
    if (p->max_numparam > NO_PARAM) {
        /* current and outer are exclusive */
        local->numparam.current = local->numparam.outer;
        local->numparam.outer = 0;
    }
    else {
        /* no numbered parameter */
        local->numparam.current = 0;
    }
    local->it = 0;
}

static const struct vtable *
dyna_push(struct parser_params *p)
{
    p->lvtbl->args = vtable_alloc(p->lvtbl->args);
    p->lvtbl->vars = vtable_alloc(p->lvtbl->vars);
    if (p->lvtbl->used) {
        p->lvtbl->used = vtable_alloc(p->lvtbl->used);
    }
    return p->lvtbl->args;
}

static void
dyna_pop_vtable(struct parser_params *p, struct vtable **vtblp)
{
    struct vtable *tmp = *vtblp;
    *vtblp = tmp->prev;
# if WARN_PAST_SCOPE
    if (p->past_scope_enabled) {
        tmp->prev = p->lvtbl->past;
        p->lvtbl->past = tmp;
        return;
    }
# endif
    vtable_free(tmp);
}

static void
dyna_pop_1(struct parser_params *p)
{
    struct vtable *tmp;

    if ((tmp = p->lvtbl->used) != 0) {
        warn_unused_var(p, p->lvtbl);
        p->lvtbl->used = p->lvtbl->used->prev;
        vtable_free(tmp);
    }
    dyna_pop_vtable(p, &p->lvtbl->args);
    dyna_pop_vtable(p, &p->lvtbl->vars);
}

static void
dyna_pop(struct parser_params *p, const struct vtable *lvargs)
{
    while (p->lvtbl->args != lvargs) {
        dyna_pop_1(p);
        if (!p->lvtbl->args) {
            struct local_vars *local = p->lvtbl->prev;
            ruby_xfree_sized(p->lvtbl, sizeof(*p->lvtbl));
            p->lvtbl = local;
        }
    }
    dyna_pop_1(p);
}

static int
dyna_in_block(struct parser_params *p)
{
    return !DVARS_TERMINAL_P(p->lvtbl->vars) && p->lvtbl->vars->prev != DVARS_TOPSCOPE;
}

static int
dvar_defined_ref(struct parser_params *p, ID id, ID **vidrefp)
{
    struct vtable *vars, *args, *used;
    int i;

    args = p->lvtbl->args;
    vars = p->lvtbl->vars;
    used = p->lvtbl->used;

    while (!DVARS_TERMINAL_P(vars)) {
        if (vtable_included(args, id)) {
            return 1;
        }
        if ((i = vtable_included(vars, id)) != 0) {
            if (used && vidrefp) *vidrefp = &used->tbl[i-1];
            return 1;
        }
        args = args->prev;
        vars = vars->prev;
        if (!vidrefp) used = 0;
        if (used) used = used->prev;
    }

    if (vars == DVARS_INHERIT && !NUMPARAM_ID_P(id)) {
        return 0; /* PORTME: outer eval scopes arrive with the scopes option */
    }

    return 0;
}

static int
dvar_defined(struct parser_params *p, ID id)
{
    return dvar_defined_ref(p, id, NULL);
}

static int
dvar_curr(struct parser_params *p, ID id)
{
    return (vtable_included(p->lvtbl->args, id) ||
            vtable_included(p->lvtbl->vars, id));
}

static void
reg_fragment_enc_error(struct parser_params* p, rb_parser_string_t *str, int c)
{
    YSTUB("reg_fragment_enc_error");
    return;
}

static rb_encoding *
find_enc(struct parser_params* p, const char *name)
{
    YSTUB("find_enc");
    return NULL;
}

static rb_encoding *
kcode_to_enc(struct parser_params* p, int kcode)
{
    YSTUB("kcode_to_enc");
    return NULL;
}

int
rb_reg_fragment_setenc(struct parser_params* p, rb_parser_string_t *str, int options)
{
    YSTUB("rb_reg_fragment_setenc");
    return 0;
}

static void
reg_fragment_setenc(struct parser_params* p, rb_parser_string_t *str, int options)
{
    YSTUB("reg_fragment_setenc");
    return;
}

typedef struct {
    struct parser_params* parser;
    rb_encoding *enc;
    NODE *succ_block;
    const YYLTYPE *loc;
    rb_parser_assignable_func assignable;
} reg_named_capture_assign_t;



static NODE *
reg_named_capture_assign(struct parser_params* p, VALUE regexp, const YYLTYPE *loc, rb_parser_assignable_func assignable)
{
    YSTUB("reg_named_capture_assign");
    return NULL;
}

static NODE *
rb_parser_assignable(struct parser_params *p, ID id, NODE *val, const YYLTYPE *loc)
{
    YSTUB("rb_parser_assignable");
    return NULL;
}

static int
rb_reg_named_capture_assign_iter_impl(struct parser_params *p, const char *s, long len,
                                      rb_encoding *enc, NODE **succ_block, const rb_code_location_t *loc, rb_parser_assignable_func assignable)
{
    YSTUB("rb_reg_named_capture_assign_iter_impl");
    return 0;
}

static VALUE
parser_reg_compile(struct parser_params* p, rb_parser_string_t *str, int options)
{
    YSTUB("parser_reg_compile");
    return 0;
}

static VALUE
rb_parser_reg_compile(struct parser_params* p, VALUE str, int options)
{
    YSTUB("rb_parser_reg_compile");
    return 0;
}

static VALUE
reg_compile(struct parser_params* p, rb_parser_string_t *str, int options)
{
    YSTUB("reg_compile");
    return 0;
}


static NODE *
parser_append_options(struct parser_params *p, NODE *node)
{
    YSTUB("parser_append_options");
    return NULL;
}

static void
rb_init_parse(void)
{
    /* nothing global to initialize */
}

static ID
internal_id(struct parser_params *p)
{
    YSTUB("internal_id");
    return 0;
}






/* CRuby re-exports rb_reserved_word after undefining the lex.c macro; every
 * caller here goes through the macro to the static gperf table directly. */













static size_t
count_char(const char *str, int c)
{
    int n = 0;
    while (str[n] == c) n++;
    return n;
}

/*
 * strip enclosing double-quotes, same as the default yytnamerr except
 * for that single-quotes matching back-quotes do not stop stripping.
 *
 *  "\"`class' keyword\"" => "`class' keyword"
 */
size_t
rb_yytnamerr(struct parser_params *p, char *yyres, const char *yystr)
{
    YSTUB("rb_yytnamerr");
    return 0;
}

/*
 * Local variables:
 * mode: c
 * c-file-style: "ruby"
 * End:
 */

/*
 * THE DRIVER. This section replaces CRuby's yycompile/yycompile0 and the
 * rb_parser_compile_* entry points: prism hands us a pm_parser_t whose source
 * is entirely in memory, we run the grammar over it, and everything reachable
 * from the returned tree lives in that parser's arenas.
 */

/* Record that the parse crossed a construct whose node building has not been
 * ported yet. One diagnostic per parse is enough to fail the differential
 * tests and to tell the user what they hit first. */
static void
pm_yparse_stub(struct parser_params *p, const char *name)
{
    if (p->error_p) return;
    p->error_p = 1;

    char message[128];
    snprintf(message, sizeof(message), "the parse_y backend cannot build this yet: %s", name);

    pm_diagnostic_list_append_format(
        &p->pm->metadata_arena, &p->pm->error_list,
        YOFF(p->lex.ptok), (uint32_t) (p->lex.pcur - p->lex.ptok),
        PM_ERR_PARSEY_SYNTAX, message);
}

/*
 * Build the ProgramNode that wraps what the grammar produced. Mirrors the
 * tail of parse_program() in src/prism.c: even an empty or failed parse
 * yields a ProgramNode with a StatementsNode so that consumers can rely on
 * the shape of the tree.
 */
static pm_node_t *
pm_yparse_program(struct parser_params *p, pm_node_t *tree)
{
    pm_parser_t *pm = p->pm;

    if (tree != NULL && PM_NODE_TYPE_P(tree, PM_PROGRAM_NODE)) {
        return tree;
    }

    pm_statements_node_t *body;
    if (tree != NULL && PM_NODE_TYPE_P(tree, PM_STATEMENTS_NODE)) {
        body = (pm_statements_node_t *) tree;
    }
    else {
        body = pm_statements_node_new(pm->arena, ++pm->node_id, 0, (pm_location_t) { 0 }, (pm_node_list_t) { 0 });
    }

    pm_constant_id_list_t locals = { 0 };
    return (pm_node_t *) pm_program_node_new(pm->arena, ++pm->node_id, 0, body->base.location, locals, body);
}

/*
 * Parse the Ruby source associated with the given parser with this grammar
 * and return the tree. The entry point behind PM_OPTIONS_BACKEND_PARSE_Y.
 */
pm_node_t *
pm_yparse(pm_parser_t *pm)
{
    struct parser_params params;
    struct parser_params *p = &params;

    memset(p, 0, sizeof(params));
    p->pm = pm;

    /* parser_initialize, minus the fields the fork removed. */
    p->command_start = TRUE;
    p->lex.lpar_beg = -1; /* make lambda_beginning_p() == FALSE at first */
    p->node_id = 0;
    p->frozen_string_literal = pm->frozen_string_literal;
    p->enc = pm->encoding;
    p->exits = 0;

    /* yycompile, minus the source file bookkeeping prism already did. */
    p->ruby_sourceline = 0;
    p->lvtbl = NULL;
    p->lex.gets_cursor = (const char *) pm->start;

    p->do_print = (pm->command_line & PM_OPTIONS_COMMAND_LINE_P) != 0;
    p->do_loop = (pm->command_line & (PM_OPTIONS_COMMAND_LINE_P | PM_OPTIONS_COMMAND_LINE_N)) != 0;
    p->do_chomp = (pm->command_line & PM_OPTIONS_COMMAND_LINE_L) != 0;
    p->do_split = (pm->command_line & PM_OPTIONS_COMMAND_LINE_A) != 0;

    /* yycompile0. */
    parser_prepare(p);
    yyparse(p);

    /* A reported error means some action could not build its node; anything
     * downstream of that point may hold NULLs where required children belong,
     * so only the guaranteed-consistent empty program is safe to hand out. */
    pm_node_t *tree = pm_yparse_program(p, p->error_p ? NULL : p->eval_tree);

    /* Everything below is transient state the parse allocated outside the
     * arenas; the tree itself is arena-allocated and survives. */
    xfree(p->lex.strterm);
    p->lex.strterm = 0;
    xfree(p->tokenbuf);
    while (p->lvtbl) {
        local_pop(p);
    }
    while (p->token_info) {
        token_info_pop(p, "unclosed token", &NULL_LOC);
    }

    return tree;
}

/*
 * LOCATIONS. The setters the lexer publishes token locations through, in byte
 * offsets. Where CRuby computes a (line, column) pair, the fork subtracts
 * pointers into the source; see the header comment.
 */

static YYLTYPE *
rb_parser_set_pos(YYLTYPE *yylloc, uint32_t beg, uint32_t end)
{
    yylloc->beg = beg;
    yylloc->end = end;
    return yylloc;
}

static YYLTYPE *
rb_parser_set_location_from_strterm_heredoc(struct parser_params *p, rb_strterm_heredoc_t *here, YYLTYPE *yylloc)
{
    uint32_t line = YOFF(PM_YSTRING_PTR(here->lastline));
    uint32_t beg = line + (uint32_t) here->offset - here->quote
        - (3 - !(here->func & STR_FUNC_INDENT)); /* 3 = strlen("<<-") */
    uint32_t end = line + (uint32_t) here->offset + here->length + here->quote;

    return rb_parser_set_pos(yylloc, beg, end);
}

static YYLTYPE *
rb_parser_set_location_of_heredoc_end(struct parser_params *p, YYLTYPE *yylloc)
{
    return rb_parser_set_pos(yylloc, YOFF(p->lex.ptok), YOFF(p->lex.pend));
}

static YYLTYPE *
rb_parser_set_location_of_none(struct parser_params *p, YYLTYPE *yylloc)
{
    return rb_parser_set_pos(yylloc, YOFF(p->lex.ptok), YOFF(p->lex.ptok));
}

static YYLTYPE *
rb_parser_set_location(struct parser_params *p, YYLTYPE *yylloc)
{
    return rb_parser_set_pos(yylloc, YOFF(p->lex.ptok), YOFF(p->lex.pcur));
}

/*
 * DIAGNOSTICS. Errors append to the prism parser's error list, which is what
 * pm_serialize and the Ruby-level ParseResult read. CRuby's error path also
 * renders the offending source line into the message; prism's consumers do
 * that themselves from the location, so only the message itself is kept.
 */

static int
parser_yyerror(struct parser_params *p, const YYLTYPE *yylloc, const char *msg)
{
    YYLTYPE current;
    if (!yylloc) {
        yylloc = RUBY_SET_YYLLOC(current);
    }
    pm_diagnostic_list_append_format(
        &p->pm->metadata_arena, &p->pm->error_list,
        yylloc->beg, yylloc->end - yylloc->beg,
        PM_ERR_PARSEY_SYNTAX, msg);
    p->error_p = 1;
    return 0;
}

static int
parser_yyerror0(struct parser_params *p, const char *msg)
{
    YYLTYPE current;
    RUBY_SET_YYLLOC(current);
    return parser_yyerror(p, &current, msg);
}

static void
parser_compile_error(struct parser_params *p, const rb_code_location_t *loc, const char *fmt, ...)
{
    char message[256];
    va_list args;

    va_start(args, fmt);
    vsnprintf(message, sizeof(message), fmt, args);
    va_end(args);

    YYLTYPE current;
    if (!loc) {
        RUBY_SET_YYLLOC(current);
        loc = &current;
    }

    pm_diagnostic_list_append_format(
        &p->pm->metadata_arena, &p->pm->error_list,
        loc->beg, loc->end - loc->beg,
        PM_ERR_PARSEY_SYNTAX, message);
    p->error_p = 1;
}
