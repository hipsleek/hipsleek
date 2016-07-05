#include "xdebug.cppo"
open Camlp4.PreCast

type lemma_kind_t = TLEM_TEST | TLEM_PROP | TLEM_SPLIT | TLEM_TEST_NEW | TLEM | TLEM_UNSAFE | TLEM_INFER | TLEM_INFER_PRED | TLEM_SAFE

type sleek_token =
  | IDENTIFIER    of string
  | INT_LITER     of int * string
  | FLOAT_LIT     of float * string
  | FRAC_LIT of   Frac.frac * string
  | CHAR_LIT      of char * string
  | STRING        of string * string
  (*| COMMENT       of string*)
  | EOF 
  | JAVA          of string
  | LEMMA         of lemma_kind_t
  | RLEMMA
  (*keywords*)
  | ANDLIST| ABSTRACT
  | ASSERT | ASSERT_EXACT | ASSERT_INEXACT | ASSUME | INFER_ASSUME | ALLN | APPEND | AXIOM (* [4/10/2011] An Hoa *)
  | BIND | BOOL | BREAK | BAGMAX | BAGMIN | BAG | BARRIER 
  | PASS_COPY
  | SLK_HULL | SLK_PAIRWISE
  | CASE | SIMPLIFY | CAPTURERESIDUE | CLASS | COMPOSE | CONST | CONTINUE
  | CHECKNORM | CHECKEQ | CHECKSAT | CHECK_NONDET 
  | CHECKENTAIL |  CHECKENTAIL_EXACT | CHECKENTAIL_INEXACT
  | DATA | DDEBUG | DIFF | DYNAMIC 
  | RELASSUME | RELDEFN 
  | SHAPE_INFER | SHAPE_INFER_PROP 
  | SHAPE_POST_OBL | SHAPE_DIVIDE | SHAPE_CONQUER |  SHAPE_LFP |  SHAPE_REC
  | SHAPE_SPLIT_BASE 
  | SHAPE_EXTRACT | SHAPE_DECL_DANG | SHAPE_DECL_UNKNOWN
  | SHAPE_STRENGTHEN_CONSEQ | SHAPE_WEAKEN_ANTE
  | SHAPE_ADD_DANGLING | SHAPE_UNFOLD | SHAPE_PARAM_DANGLING 
  | SHAPE_SIMPLIFY | SHAPE_MERGE | SHAPE_TRANS_TO_VIEW
  | SHAPE_DERIVE_PRE (* to derive pre-predicate into view *)
  | SHAPE_DERIVE_POST (* to derive post-predicate into view *)
  | SHAPE_DERIVE_VIEW
  | SHAPE_EXTN_VIEW
  | SHAPE_NORMALIZE
  | DATA_MARK_REC
  | PRED_ELIM_HEAD
  | PRED_ELIM_TAIL
  | PRED_UNIFY_DISJ
  | PRED_SPEC 
  | PRED_SPLIT  
  | PRED_NORM_SEG | PRED_NORM_DISJ
  | PRED_ELIM_USELESS (* should be PRED_ELIM_USELESS *) 
  | PRED_REUSE
  | PRED_REUSE_SUBS
  | PRED_UNFOLD
  | REL_INFER
  | DTIME
  | ELSE_TT
  | EMPTY
  | ENSURES | ENSURES_EXACT | ENSURES_INEXACT | ENUM | EXISTS | EXPECT_INFER
  | EXTENDS 
  (* | EXTENDS_REC *)
  | FALSE | FLOAT | FORALL | FUNC
  | HP | HPPOST
  | HTRUE
  | IF 
  | IN_T | INT | INFINT_TYPE | INTERSECT | INV | INLINE (* An Hoa [22/08/2011] : inline keyword for inline field declaration in structures *)
  | INV_EXACT | INV_SAT | BG
  | ANN_KEY
  | LET
  | MAX | MIN 
  | NEW | NOTIN | NULL
  | OFF | ON | ORWORD | ANDWORD
  | PRED | PRED_PRIM | DPRINT | PRED_EXT 
  | PRINT | PRINT_LEMMAS | CMP | HIP_INCLUDE
  (* | PRINT_VIEW *)
  (* | PRINT_VIEW_LONG *)
  | PASS_REF | PASS_REF2 |REL | REQUIRES (*| REQUIRESC*) | RES of string | RETURN
  | SELFT of string | SPLIT | SUBSET | STATIC
  | THEN | THIS of string | TO | TRUE | LEXVAR
  | TEMPL | TERM | LOOP | MAYLOOP (* | TERMU | TERMR *) 
  | TERM_INFER 
  (* | TREL_INFER  change to  INFER_AT_TERM *)
  | TREL_ASSUME
  | INFER_AT_EFA | INFER_AT_DFA | INFER_AT_CLASSIC | INFER_AT_PAR | INFER_AT_ERRMUST | INFER_AT_ERRMUST_ONLY | INFER_AT_ERRMAY | INFER_AT_DE_EXC | INFER_AT_PREMUST
  | INFER_AT_VER_POST
  | INFER_AT_TERM | INFER_AT_TERM_WO_POST | INFER_AT_FIELD_IMM
  | INFER_AT_PRE | INFER_AT_POST | INFER_AT_IMM | INFER_AT_SHAPE | INFER_AT_SHAPE_PRE | INFER_AT_SHAPE_POST | INFER_AT_SHAPE_PRE_POST
  | INFER_AT_ERROR | INFER_AT_FLOW | INFER_AT_PURE_FIELD
  | INFER_AT_SIZE | INFER_ANA_NI
  | INFER_AT_ARR_AS_VAR 
  | INFER_IMM_PRE | INFER_IMM_POST
  | UTPRE | UTPOST
  | UIPRE | UIPOST
  | UNFOLD | UNION
  | VOID 
  | WHILE | FLOW of string
  (*operators*)  
  | CARET 
  | DOTDOT | ATPOS
  | ACCS | AND | ANDSTAR | ANDAND | UNIONSTAR | STARMINUS | AT | ATATSQ | ATAT | LEND | IMM | MUT | MAT | DERV | SPLIT1Ann | SPLIT2Ann | CBRACE | CLIST | COLON | COLONCOLON | COLONCOLONCOLON | COMMA | CPAREN | CSQUARE | DOLLAR  (* | VAL | REC *)
  (* TermInf: Token for Termination Inference *)
  | TEMPLATE | TEMPL_SOLVE
  | NI | RO
  | DOT | DOUBLEQUOTE | EQ | EQEQ | RIGHTARROW | EQUIV | GT | GTE | HASH | REL_GUARD | HEAD | INLIST | LEFTARROW | LENGTH
  | LT | LTE | MINUS | MEM | MEME | NEQ | NOT | NOTINLIST | OBRACE |OLIST | OPAREN | OP_ADD_ASSIGN | OP_DEC | OP_DIV_ASSIGN 
  | OP_INC | OP_MOD_ASSIGN | OP_MULT_ASSIGN | OP_SUB_ASSIGN | OR | OROR | PERM | DERIVE | EQV | CONSTR | OSQUARE  | REVERSE | SET | TAIL 
  (* | TOPAREN | TCPAREN *)
  | PERCENT | PMACRO 
  | PZERO | PFULL | PVALUE | PLEND | PCONST of Frac.frac |PFRAC (* | PREF *)
  | SPLITANN
  | TUP2
  | PLUS | PRIME 
  | SEMICOLON | SAT | SPEC
  | STAR | DIV
  | GLOBAL |VARIANCE| ESCAPE | HPRED | REFINES | JOIN | WITH | COMBINE | FINALIZE | TRY | CATCH | FINALLY | THROWS | RAISE
  | INFER | INFER_EXACT | INFER_INEXACT | SUBANN | XPRE | PRE | XPOST | POST
  | INVLOCK 
  | LOGICAL
  | INFINITY
  | NEGINFINITY
  | VALIDATE
  | VALID |SSAT | SUNSAT
  | FAIL
  | FAIL_MUST
  | FAIL_MAY
  | XPURE
  | PAR
  | ARGOPTION of string
  (* | SKIP - should be an identifier! *)
(* | IN_RFLOW | OUT_RFLOW (* For HO resource reasoning *) *)


module type SleekTokenS = Camlp4.Sig.Token with type t = sleek_token

module Token = struct
  open Format
  module Loc = Loc
  type t = sleek_token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with 
    | IDENTIFIER s | INT_LITER (_,s) | FLOAT_LIT (_,s)  | CHAR_LIT (_,s) | STRING (_,s)-> s | FRAC_LIT (_, s) -> s
    (*| COMMENT s -> "/* "^s^" */"*)
    | EOF -> ""
    | JAVA s-> s
    | AXIOM -> "axiom" (* [4/10/2011] An Hoa *)
    | ANDLIST -> "AndList" | ATPOS -> "at"
    | ASSERT -> "assert" | ASSERT_EXACT -> "assert_exact" | ASSERT_INEXACT -> "assert_inexact" | ASSUME -> "assume" | INFER_ASSUME -> "infer_assume" | ALLN-> "alln" | APPEND -> "app" | ABSTRACT -> "abstract"
    | BIND -> "bind"| BOOL -> "bool" | BREAK ->"break" | BAGMAX ->"bagmax" | BAGMIN->"bagmin" | BAG->"bag" | BARRIER ->"barrier"
    | CASE ->"case" | CHECKNORM -> "check_normalize" | CHECKEQ -> "checkeq" | CHECKENTAIL ->"checkentail" | CAPTURERESIDUE ->"capture_residue" | CLASS ->"class" | CLIST -> "|]" | PASS_COPY -> "@C"(* | COERCION ->"coercion" *)
    | CHECKENTAIL_EXACT -> "checkentail_exact" | CHECKENTAIL_INEXACT -> "checkentail_inexact"
    | CHECK_NONDET -> "check_nondet"
    | CHECKSAT -> "checksat"
    | RELASSUME -> "relAssume" | RELDEFN -> "relDefn"    | SHAPE_INFER -> "shape_infer" |  SHAPE_INFER_PROP -> "shape_infer_proper" | SHAPE_POST_OBL -> "shape_post_obligation" | SHAPE_DIVIDE -> "shape_divide" | SHAPE_CONQUER -> "shape_conquer" |  SHAPE_LFP -> "shape_lfp" |  SHAPE_REC -> "shape_rec"
    | SHAPE_SPLIT_BASE -> "shape_split_base" 
    | SHAPE_EXTRACT -> "shape_extract"
    | SHAPE_DECL_DANG -> "Declare_Dangling" | SHAPE_DECL_UNKNOWN -> "Declare_Unknown"
    | SHAPE_STRENGTHEN_CONSEQ -> "shape_strengthen_conseq"
    | SHAPE_WEAKEN_ANTE -> "shape_weaken_ante"
    | SHAPE_ADD_DANGLING -> "shape_add_dangling"
    | SHAPE_UNFOLD -> "shape_unfold"
    | SHAPE_PARAM_DANGLING -> "shape_param_dangling"
    | SHAPE_SIMPLIFY -> "shape_simplify"
    | SHAPE_MERGE -> "shape_merge"
    | SHAPE_TRANS_TO_VIEW -> "shape_trans_to_view"
    | SHAPE_DERIVE_PRE -> "shape_derive_pre"
    | SHAPE_DERIVE_POST -> "shape_derive_post"
    | SHAPE_DERIVE_VIEW -> "shape_derive_view"
    | SHAPE_EXTN_VIEW -> "shape_extends_view"
    | SHAPE_NORMALIZE -> "shape_normalize"
    | DATA_MARK_REC -> "data_mark_rec"
    | PRED_ELIM_HEAD -> "pred_elim_hd_node"
    | PRED_ELIM_TAIL -> "pred_elim_tl_node"
    | PRED_UNIFY_DISJ -> "pred_unify_disj"
    | PRED_ELIM_USELESS -> "pred_elim_useless" 
    | PRED_REUSE -> "pred_reuse" 
    | PRED_REUSE_SUBS -> "pred_reuse_subs" 
    | PRED_UNFOLD -> "pred_unfold" 
    | PRED_SPLIT -> "pred_split" | PRED_NORM_DISJ ->  "pred_norm_disj" 
    | PRED_SPEC ->"pred_spec" | PRED_NORM_SEG -> "pred_norm_seg"
    | REL_INFER -> "relation_infer" | SPEC -> "spec"
    | SIMPLIFY -> "simplify" | SLK_HULL -> "slk_hull"  | SLK_PAIRWISE -> "slk_pairwise"
    | COMPOSE ->"compose" | CONST ->"const" | CONTINUE ->"continue"	| DATA ->"data" | DDEBUG ->"debug" | DIFF ->"diff"| DYNAMIC ->"dynamic"
    | DTIME ->"time" | ELSE_TT ->"else" | EMPTY -> "emp"| ENSURES ->"ensures" | ENSURES_EXACT ->"ensures_exact" | ENSURES_INEXACT ->"ensures_inexact" | ENUM ->"enum"| EXISTS ->"ex" | EXTENDS ->"extends" | EXPECT_INFER -> "expect_infer"
    | FALSE ->"false"| FLOAT ->"float" | FORALL ->"forall" | FUNC -> "ranking"
    | HTRUE -> "htrue"
    | HP->"HeapPred" | HPPOST->"PostPred"
    | IF ->"if" | IN_T ->"in" | INT ->"int"| INFINT_TYPE ->"INFint"| INTERSECT ->"intersect" | INV->"inv" | INLINE ->"inline" (* An Hoa : inline added *)
    | RLEMMA -> "rlemma"
    | ANN_KEY -> "ann"
    | INV_EXACT -> "inv_exact" | INV_SAT -> "inv_sat" | BG -> "BG"
    | LEMMA TLEM ->"lemma" | LEMMA TLEM_TEST ->"lemma_test" | LEMMA TLEM_TEST_NEW ->"lemma_test_new" | LEMMA TLEM_UNSAFE ->"lemma_unsafe" (* | LEMMA true -> "lemma_exact"  *)
    | LEMMA TLEM_SPLIT ->"lemma_split"
    | LEMMA TLEM_PROP ->"lemma_prop"
    | LEMMA TLEM_SAFE ->"lemma_safe" | LEMMA TLEM_INFER ->"lemma_infer" | LEMMA TLEM_INFER_PRED ->"lemma_infer_pred" | LET->"let" | MAX ->"max" | MIN ->"min" | NEW ->"new" | NOTIN ->"notin" | NULL ->"null"
    | OFF ->"off" | ON->"on" | ORWORD ->"or" | ANDWORD ->"and" | PRED ->"pred" | PRED_PRIM -> "pred_prim" | PRED_EXT ->"pred_extn" | HIP_INCLUDE -> "hip_include" | DPRINT ->"dprint" 
    | PRINT -> "print" 
    | PRINT_LEMMAS -> "print_lemmas" 
    (* | PRINT_VIEW -> "print_view"  *)
    (* | PRINT_VIEW_LONG -> "print_view_long"  *)
    |CMP -> "sleek compare" | PASS_REF ->"@R" | PASS_REF2 ->"ref"|REL->"relation" |REQUIRES ->"requires" | RES s->"res "^s 
    | RETURN->"return" | SELFT s ->"self "^s | SPLIT ->"split"| SUBSET ->"subset" | STATIC ->"static" | LEXVAR ->"LexVar"
    | THEN->"then" | THIS s->"this "^s | TO ->"to" | TRUE ->"true" | UNFOLD->"unfold" | UNION->"union"
    | VOID->"void" | WHILE ->"while" | FLOW s->"flow "^s
    (*operators*)
    | NI ->"@NI" | RO ->"@RO" | ATATSQ -> "@@[" | CARET -> "^"
    | DOTDOT ->".."
    | AND ->"&"  | ANDAND ->"&&" | ANDSTAR -> "&*" |  UNIONSTAR ->"U*" | STARMINUS -> "--@"| AT ->"@"  | ATAT -> "@@" | LEND->"@L" | ACCS ->"@A" | IMM->"@I"| DERV->"@D"| SPLIT1Ann ->"@S1" | SPLIT2Ann ->"@S2" | CBRACE ->"}"| COLON ->":"| COLONCOLON ->"::"| COLONCOLONCOLON -> ":::" | COMMA ->","| CPAREN->")" | CSQUARE ->"]" |PFRAC -> "@frac"(* | VAL ->"@VAL" | REC ->"@REC"*)
    | TEMPLATE -> "template" | TEMPL_SOLVE -> "template_solve"
    | DOLLAR ->"$" | DOT ->"." | DOUBLEQUOTE ->"\"" | DIV -> "/" | EQ ->"=" | EQEQ -> "==" | RIGHTARROW -> "<-"| EQUIV ->"<->" | GT ->">" | GTE ->">= " | HASH ->"#" | REL_GUARD -> "|#|"
    | LEFTARROW -> "->" | LT -> "<" | LTE -> "<=" | MINUS -> "-" | NEQ -> "!=" | NOT -> "!" | OBRACE ->"{" | OLIST -> "[|" | OPAREN ->"(" | OP_ADD_ASSIGN -> "+=" | OP_DEC -> "--"
    | OP_DIV_ASSIGN -> "\\=" | OP_INC -> "++" | OP_MOD_ASSIGN -> "%=" | OP_MULT_ASSIGN ->"*=" | OP_SUB_ASSIGN -> "-=" | OR -> "|" | OROR -> "||" 
    | DERIVE -> "|-" | EQV -> "-|-" | CONSTR -> "-->" |  OSQUARE -> "[" | PERCENT ->"%" | PMACRO -> "PMACRO" | PLUS -> "+" | PRIME -> "'" | SEMICOLON -> ";" | STAR -> "*"
    | RAISE -> "raise" | THROWS -> "throws" | FINALLY -> "finally" | COMBINE -> "combine" | WITH -> "with" | JOIN -> "joinpred" | REFINES -> "refines"
    | HPRED -> "ho_pred" | ESCAPE -> "escape" | VARIANCE -> "variance" | GLOBAL -> "global" | TAIL -> "tail" | SET -> "set" | REVERSE -> "reverse"
    | PERM -> "perm" | NOTINLIST -> "notinlist" | CATCH -> "catch" | TRY -> "try" | FINALIZE -> "finalizes" | LENGTH -> "len" | INLIST -> "inlist" | HEAD -> "head"
    | MEM -> "mem" | MEME -> "memE"
    | INFER -> "infer" | INFER_EXACT -> "infer_exact" | INFER_INEXACT -> "infer_inexact"
    | PRE -> "@pre" | XPRE -> "@xpre" | MUT -> "@M" | MAT -> "@R" | POST -> "@post" | XPOST -> "@xpost" | SUBANN -> "<:" | SAT -> "@S"
    (* | PREF -> "@p_ref" *) | PVALUE -> "@value" | PFULL -> "@full" | PZERO -> "@zero" | PLEND -> "@lend" | PCONST f -> "@" ^ (Frac.string_of_frac f)
    | SPLITANN -> "@Split"
    | TUP2 -> "tup2"
    | INVLOCK->"inv_lock"
    | LOGICAL -> "logical"
    | INFINITY -> "\\inf"
    | NEGINFINITY -> "~\\inf"
    | TEMPL ->"template"
    | TERM -> "Term"
    | LOOP -> "Loop"
    | MAYLOOP -> "MayLoop"
    | VALIDATE -> "expect"
    | VALID -> "Valid"
    | SSAT -> "Sat"
    | SUNSAT -> "Unsat"
    | FAIL -> "Fail"
    | FAIL_MUST -> "Fail_Must"
    | FAIL_MAY -> "Fail_May"
    (* | TERMU -> "TermU" *)
    (* | TERMR -> "TermR" *)
    | UTPRE -> "UTPre"
    | UTPOST -> "UTPost"
    | UIPRE -> "UImmPre"
    | UIPOST -> "UImmPost"
    (* | TREL_INFER -> "@term" *)
    | INFER_AT_EFA -> "@efa"
    | INFER_AT_DFA -> "@dfa"
    | INFER_AT_TERM -> "@term"
    | INFER_AT_ERRMUST -> "@err_must"
    | INFER_AT_PREMUST -> "@pre_must"
    | INFER_AT_ERRMUST_ONLY -> "@err_must_only"
    | INFER_AT_DE_EXC -> "@dis_err"
    | INFER_AT_ERRMAY -> "@err_may"
    | INFER_AT_TERM_WO_POST -> "@term_wo_post"
    | INFER_AT_PRE -> "@pre_n"
    | INFER_AT_POST -> "@post_n"
    | INFER_AT_VER_POST -> "@ver_post"
    | INFER_AT_CLASSIC -> "@leak"
    | INFER_AT_PAR -> "@par"
    | INFER_AT_IMM -> "@imm"
    | INFER_AT_PURE_FIELD -> "@pure_field"
    | INFER_AT_FIELD_IMM -> "@field_imm"
    | INFER_AT_ARR_AS_VAR -> "@arrvar"
    | INFER_AT_SHAPE -> "@shape"
    | INFER_AT_SHAPE_PRE -> "@shape_pre"
    | INFER_AT_SHAPE_POST -> "@shape_post"
    | INFER_AT_SHAPE_PRE_POST -> "@shape_prepost"
    | INFER_AT_ERROR -> "@error"
    | INFER_AT_FLOW -> "@flow"
    | INFER_AT_SIZE -> "@size"
    | INFER_ANA_NI -> "@ana_ni"
    | INFER_IMM_PRE -> "@imm_pre"
    | INFER_IMM_POST -> "@imm_post"
    | TREL_ASSUME -> "termAssume"
    | TERM_INFER -> "term_infer"
    | XPURE -> "XPURE"
    (* | "<#" { TOPAREN } *) (* replaced by `LT;`HASH. inline\data-holes.lsk. examples/fracperm/thread/thrd1.slk*)
    (* | "#>" { TCPAREN } (\*Open and close paren for thread heap*\) *) (* replaced by `HASH;`GT*)
    | PAR -> "par"
    | ARGOPTION arg -> "##OPTION "^arg
  (* | SKIP -> "skip" *)
  (* | IN_RFLOW -> "-%" | OUT_RFLOW -> "+%" *)

  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false 

  let extract_string t = match t with
    | IDENTIFIER s | INT_LITER (_,s) | FLOAT_LIT (_,s) | FRAC_LIT (_, s) 
    | CHAR_LIT (_,s) | STRING (_,s) (*| COMMENT s*) | JAVA s | RES s | SELFT s | THIS s | FLOW s -> s
    | _ -> ""


  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

    type t =
      { is_kwd : string -> bool;
        mutable filter : token_filter }

    let mk is_kwd =
      { is_kwd = is_kwd;
        filter = (fun s -> s) }

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end

end
module Error = Camlp4.Struct.EmptyError
