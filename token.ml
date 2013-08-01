open Camlp4.PreCast

type sleek_token =
  | IDENTIFIER    of string
  | INT_LITER     of int * string
  | FLOAT_LIT     of float * string
  | CHAR_LIT      of char * string
  | STRING        of string * string
  (*| COMMENT       of string*)
  | EOF 
  | JAVA          of string
  | LEMMA 		  of bool
  (*keywords*)
  | ANDLIST
  | ASSERT | ASSERT_EXACT | ASSERT_INEXACT | ASSUME | ALLN | APPEND | AXIOM (* [4/10/2011] An Hoa *)
  | BIND | BOOL | BREAK | BAGMAX | BAGMIN | BAG | BARRIER 
  | CASE | CHECKEQ | CHECKENTAIL | CHECKENTAIL_EXACT | CHECKENTAIL_INEXACT | CAPTURERESIDUE | CLASS (* | COERCION *) | COMPOSE | CONST | CONTINUE
	| DATA | DDEBUG | DIFF | DYNAMIC 
  | RELASSUME | RELDEFN 
  | SHAPE_INFER | SHAPE_INFER_PROP | SHAPE_POST_OBL | SHAPE_DIVIDE | SHAPE_CONQUER
  | SHAPE_SPLIT_BASE | SHAPE_ELIM_USELESS | SHAPE_EXTRACT | SHAPE_DECL_DANG | SHAPE_DECL_UNKNOWN
  | SHAPE_STRENGTHEN_CONSEQ | SHAPE_WEAKEN_ANTE
  | DTIME
  | ELSE_TT
  | EMPTY
  | ENSURES | ENSURES_EXACT | ENSURES_INEXACT | ENUM | EXISTS | EXTENDS
  | FALSE | FLOAT | FORALL | FUNC
  | HP | HPPOST
  | HTRUE
	| IF 
  | IN_T | INT | INFINT_TYPE | INTERSECT | INV | INLINE (* An Hoa [22/08/2011] : inline keyword for inline field declaration in structures *)
  | LET
  | MAX | MIN 
  | NEW | NOTIN | NULL
  | OFF | ON | ORWORD | ANDWORD
	| PRED | PRED_PRIM | DPRINT | PRED_EXT | PRINT | CMP | HIP_INCLUDE
	| REF |REL | REQUIRES (*| REQUIRESC*) | RES of string | RETURN
	| SELFT of string | SPLIT | SUBSET | STATIC
  | THEN| THIS of string | TO | TRUE | LEXVAR
  | TEMPL | TERM | LOOP | MAYLOOP
  | UNFOLD | UNION
  | VOID 
  | WHILE | FLOW of string
  (*operators*)  
  | CARET 
  | ACCS | AND | ANDSTAR | ANDAND | UNIONSTAR | STARMINUS | AT | ATATSQ | ATAT | LEND | IMM | MUT | MAT | DERV | CBRACE | CLIST | COLON | COLONCOLON | COLONCOLONCOLON | COMMA | CPAREN | CSQUARE | DOLLAR  | VAL | REC | NI
  | DOT | DOUBLEQUOTE | EQ | EQEQ | RIGHTARROW | EQUIV | GT | GTE | HASH | REL_GUARD | HEAD | INLIST | LEFTARROW | LENGTH
  | LT | LTE | MINUS | MEM | MEME | NEQ | NOT | NOTINLIST | OBRACE |OLIST | OPAREN | OP_ADD_ASSIGN | OP_DEC | OP_DIV_ASSIGN 
  | OP_INC | OP_MOD_ASSIGN | OP_MULT_ASSIGN | OP_SUB_ASSIGN | OR | OROR | PERM | DERIVE | EQV | CONSTR | OSQUARE  | REVERSE | SET | TAIL 
  | PERCENT | PMACRO 
  | PZERO | PFULL | PVALUE (* | PREF *)
  | PLUS | PRIME 
  | SEMICOLON 
  | STAR | DIV
  | GLOBAL |VARIANCE| ESCAPE | HPRED | REFINES | JOIN | WITH | COMBINE | FINALIZE | TRY | CATCH | FINALLY | THROWS | RAISE
  | INFER | INFER_EXACT | INFER_INEXACT | SUBANN | XPRE | PRE | XPOST | POST
  | INVLOCK 
  | LOGICAL
  | INFINITY
  | XPURE


module type SleekTokenS = Camlp4.Sig.Token with type t = sleek_token
  
module Token = struct
  open Format
  module Loc = Loc
  type t = sleek_token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with 
    | IDENTIFIER s | INT_LITER (_,s) | FLOAT_LIT (_,s)  | CHAR_LIT (_,s) | STRING (_,s)-> s
    (*| COMMENT s -> "/* "^s^" */"*)
    | EOF -> ""
    | JAVA s-> s
    | AXIOM -> "axiom" (* [4/10/2011] An Hoa *)
	| ANDLIST -> "AndList"
    | ASSERT -> "assert" | ASSERT_EXACT -> "assert_exact" | ASSERT_INEXACT -> "assert_inexact" | ASSUME -> "assume" | ALLN-> "alln" | APPEND -> "app" 
    | BIND -> "bind"| BOOL -> "bool" | BREAK ->"break" | BAGMAX ->"bagmax" | BAGMIN->"bagmin" | BAG->"bag" | BARRIER ->"barrier"
    | CASE ->"case" | CHECKEQ -> "checkeq" | CHECKENTAIL ->"checkentail" | CAPTURERESIDUE ->"capture_residue" | CLASS ->"class" | CLIST -> "|]" (* | COERCION ->"coercion" *)
    | CHECKENTAIL_EXACT -> "checkentail_exact" | CHECKENTAIL_INEXACT -> "checkentail_inexact"
    | RELASSUME -> "relAssume" | RELDEFN -> "relDefn"
    |  SHAPE_INFER -> "shape_infer" |  SHAPE_INFER_PROP -> "shape_infer_proper" | SHAPE_POST_OBL -> "shape_post_obligation" | SHAPE_DIVIDE -> "shape_divide" | SHAPE_CONQUER -> "shape_conquer"
    | SHAPE_SPLIT_BASE -> "shape_split_base" | SHAPE_ELIM_USELESS -> "shape_elim_useless" | SHAPE_EXTRACT -> "shape_extract"
    | SHAPE_DECL_DANG -> "Declare_Dangling" | SHAPE_DECL_UNKNOWN -> "Declare_Unknown"
    | SHAPE_STRENGTHEN_CONSEQ -> "shape_strengthen_conseq"
    | SHAPE_WEAKEN_ANTE -> "shape_weaken_ante"
    | COMPOSE ->"compose" | CONST ->"const" | CONTINUE ->"continue"	| DATA ->"data" | DDEBUG ->"debug" | DIFF ->"diff"| DYNAMIC ->"dynamic"
    | DTIME ->"time" | ELSE_TT ->"else" | EMPTY -> "emp"| ENSURES ->"ensures" | ENSURES_EXACT ->"ensures_exact" | ENSURES_INEXACT ->"ensures_inexact" | ENUM ->"enum"| EXISTS ->"ex" | EXTENDS ->"extends"
    | FALSE ->"false"| FLOAT ->"float" | FORALL ->"forall" | FUNC -> "ranking"
    | HTRUE -> "htrue"
    | HP->"HeapPred" | HPPOST->"PostPred"
    | IF ->"if" | IN_T ->"in" | INT ->"int"| INFINT_TYPE ->"INFint"| INTERSECT ->"intersect" | INV->"inv" | INLINE->"inline" (* An Hoa : inline added *)
    | LEMMA false ->"lemma" | LEMMA true -> "lemma_exact" | LET->"let" | MAX ->"max" | MIN ->"min" | NEW ->"new" | NOTIN ->"notin" | NULL ->"null"
    | OFF ->"off" | ON->"on" | ORWORD ->"or" | ANDWORD ->"and" | PRED ->"pred" | PRED_PRIM -> "pred_prim" | PRED_EXT ->"pred_extn" | HIP_INCLUDE -> "hip_include" | DPRINT ->"dprint" |PRINT -> "print" |CMP -> "sleek compare" | REF ->"ref"|REL->"relation" |REQUIRES ->"requires" | RES s->"res "^s 
    | RETURN->"return" | SELFT s ->"self "^s | SPLIT ->"split"| SUBSET ->"subset" | STATIC ->"static" | LEXVAR ->"LexVar"
    | THEN->"then" | THIS s->"this "^s | TO ->"to" | TRUE ->"true" | UNFOLD->"unfold" | UNION->"union"
    | VOID->"void" | WHILE ->"while" | FLOW s->"flow "^s
  (*operators*)
    | NI ->"@NI" | ATATSQ -> "@@[" | CARET -> "^"
    | AND ->"&"  | ANDAND ->"&&" | ANDSTAR -> "&*" |  UNIONSTAR ->"U*" | STARMINUS -> "-*" | AT ->"@"  | ATAT -> "@@" | LEND->"@L" | ACCS ->"@A" | IMM->"@I"| DERV->"@D"| CBRACE ->"}"| COLON ->":"| COLONCOLON ->"::"| COLONCOLONCOLON -> ":::" | COMMA ->","| CPAREN->")" | CSQUARE ->"]" | VAL ->"@VAL" | REC ->"@REC"
    | DOLLAR ->"$" | DOT ->"." | DOUBLEQUOTE ->"\"" | DIV -> "/" | EQ ->"=" | EQEQ -> "==" | RIGHTARROW -> "<-"| EQUIV ->"<->" | GT ->">" | GTE ->">= " | HASH ->"#" | REL_GUARD -> "|#|"
    | LEFTARROW -> "->" | LT -> "<" | LTE -> "<=" | MINUS -> "-" | NEQ -> "!=" | NOT -> "!" | OBRACE ->"{" | OLIST -> "[|" | OPAREN ->"(" | OP_ADD_ASSIGN -> "+=" | OP_DEC -> "--"
    | OP_DIV_ASSIGN -> "\\=" | OP_INC -> "++" | OP_MOD_ASSIGN -> "%=" | OP_MULT_ASSIGN ->"*=" | OP_SUB_ASSIGN -> "-=" | OR -> "|" | OROR -> "||" 
    | DERIVE -> "|-" | EQV -> "-|-" | CONSTR -> "-->" |  OSQUARE -> "[" | PERCENT ->"%" | PMACRO -> "PMACRO" | PLUS -> "+" | PRIME -> "'" | SEMICOLON -> ";" | STAR -> "*"
    | RAISE -> "raise" | THROWS -> "throws" | FINALLY -> "finally" | COMBINE -> "combine" | WITH -> "with" | JOIN -> "joinpred" | REFINES -> "refines"
    | HPRED -> "ho_pred" | ESCAPE -> "escape" | VARIANCE -> "variance" | GLOBAL -> "global" | TAIL -> "tail" | SET -> "set" | REVERSE -> "reverse"
    | PERM -> "perm" | NOTINLIST -> "notinlist" | CATCH -> "catch" | TRY -> "try" | FINALIZE -> "finalizes" | LENGTH -> "len" | INLIST -> "inlist" | HEAD -> "head"
    | MEM -> "mem" | MEME -> "memE"
    | INFER -> "infer" | INFER_EXACT -> "infer_exact" | INFER_INEXACT -> "infer_inexact"
    | PRE -> "@pre" | XPRE -> "@xpre" | MUT -> "@M" | MAT -> "@R" | POST -> "@post" | XPOST -> "@xpost" | SUBANN -> "<:"
    (* | PREF -> "@p_ref" *) | PVALUE -> "@value" | PFULL -> "@full" | PZERO -> "@zero"
    | INVLOCK->"inv_lock"
    | LOGICAL -> "logical"
    | INFINITY -> "\\inf"
    | TEMPL ->"template"
    | TERM -> "Term"
    | LOOP -> "Loop"
    | MAYLOOP -> "MayLoop"
    | XPURE -> "XPURE"


  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false 
    
  let extract_string t = match t with
     | IDENTIFIER s | INT_LITER (_,s) | FLOAT_LIT (_,s)  | CHAR_LIT (_,s) | STRING (_,s) (*| COMMENT s*) | JAVA s | RES s | SELFT s | THIS s | FLOW s -> s
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
