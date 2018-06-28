{
open Globals
open Exc.ETABLE_NFLOW

open Token
(** A signature for specialized tokens. *)
module Sig = Camlp4.Sig

module Make (Token : SleekTokenS)
= struct
  module Loc = Token.Loc
  module Token = Token

  open Lexing


  (* Error report *)
  module Error = struct

    type t =
      | Illegal_character of char
      | Illegal_escape    of string
      | Unterminated_comment
      | Unterminated_string
      | Unterminated_java
      | Comment_start
      | Comment_not_end
      | Literal_overflow of string

    exception E of t

    open Format

    let print ppf =
      function
      | Illegal_character c -> fprintf ppf "Illegal character (%s)" (Char.escaped c)
      | Illegal_escape s -> fprintf ppf "Illegal backslash escape in string or character (%s)" s
      | Unterminated_comment -> fprintf ppf "Comment not terminated"
      | Unterminated_string -> fprintf ppf "String literal not terminated"
      | Unterminated_java -> fprintf ppf "java code not terminated"
      | Literal_overflow ty -> fprintf ppf "Integer literal exceeds the range of representable integers of type %s" ty
      | Comment_start -> fprintf ppf "this is the start of a comment"
      | Comment_not_end -> fprintf ppf "this is not the end of a comment"

    let to_string x =
      let b = Buffer.create 50 in
      let () = bprintf b "%a" print x in Buffer.contents b
  end;;

  let module M = Camlp4.ErrorHandler.Register(Error) in ()

  open Error

  type context =
  { loc        : Loc.t    ;
    in_comment : bool     ;
    lexbuf     : lexbuf   ;
    buffer     : Buffer.t }

  let default_context lb =
  { loc        = Loc.ghost ;
    in_comment = false     ;
    lexbuf     = lb        ;
    buffer     = Buffer.create 256 }

  (* To buffer string literals *)

  let store c = Buffer.add_string c.buffer (Lexing.lexeme c.lexbuf)
  let istore_char c i = Buffer.add_char c.buffer (Lexing.lexeme_char c.lexbuf i)
  let buff_contents c =
    let contents = Buffer.contents c.buffer in
    Buffer.reset c.buffer; contents

  let loc c = Loc.merge c.loc (Loc.of_lexbuf c.lexbuf)
  let is_in_comment c = c.in_comment
  let in_comment c = { (c) with in_comment = true }
  let set_start_p c = c.lexbuf.lex_start_p <- Loc.start_pos c.loc
  let move_start_p shift c =
    let p = c.lexbuf.lex_start_p in
    c.lexbuf.lex_start_p <- { (p) with pos_cnum = p.pos_cnum + shift }

  let update_loc c = { (c) with loc = Loc.of_lexbuf c.lexbuf }
  let with_curr_loc f c = f (update_loc c) c.lexbuf
  let parse_nested f c =   with_curr_loc f c;   set_start_p c;    buff_contents c
  let shift n c = { (c) with loc = Loc.move `both n c.loc }
  let store_parse f c = store c ; f c c.lexbuf
  let parse f c = f c c.lexbuf

  (* Update the current location with file name and line number. *)

  let update_loc c file line absolute chars =
    let lexbuf = c.lexbuf in
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with
                  | None -> pos.pos_fname
                  | Some s -> s  in
    lexbuf.lex_curr_p <- { pos with
      pos_fname = new_file;
      pos_lnum = if absolute then line else pos.pos_lnum + line;
      pos_bol = pos.pos_cnum - chars;
    }

  let err error loc = raise(Loc.Exc_located(loc, Error.E error))

  let warn error loc = Format.eprintf "Warning: %a: %a@." Loc.print loc Error.print error

 let sleek_keywords = Hashtbl.create 100
 let comment_level = ref 0
 let _ = List.map (fun ((k,t):(string*sleek_token)) -> Hashtbl.add sleek_keywords k t)
  [("assert", ASSERT);
   ("assert_exact", ASSERT_EXACT);
   ("at", ATPOS);
   ("assert_inexact", ASSERT_INEXACT);
   ("assume", ASSUME);
   ("infer_assume", INFER_ASSUME);
   ("axiom", AXIOM); (* [4/10/2011] An Hoa : new keyword *)
   ("alln", ALLN);
   ("app", APPEND);
   ("ann", ANN_KEY);
   ("AndList", ANDLIST);
   ("abstract", ABSTRACT);
   ("bagmax", BAGMAX);
   ("bagmin", BAGMIN);
   ("bag", BAG);
   ("Barrier", BARRIER);
   ("bind", BIND);
   ("bool", BOOL);
   ("break", BREAK);
   ("case",CASE);
   ("catch", CATCH);
   ("check_normalize", CHECKNORM);
   ("checkeq", CHECKEQ);
   ("checkentail", CHECKENTAIL);
   ("checkentail_exact", CHECKENTAIL_EXACT);
   ("checkentail_inexact", CHECKENTAIL_INEXACT);
   ("checksat", CHECKSAT);
   ("check_nondet", CHECK_NONDET);
   ("slk_hull", SLK_HULL);
   ("slk_pairwise", SLK_PAIRWISE);
   ("slk_simplify", SIMPLIFY);
   (* ("slk_elim_exists", SLK_ELIM_EXISTS); (\* may weaken *\) *)
   ("relAssume", RELASSUME);
   ("relDefn", RELDEFN);
   ("shape_infer", SHAPE_INFER );
   ("shape_infer_proper", SHAPE_INFER_PROP );
   ("shape_post_obligation", SHAPE_POST_OBL);
   ("shape_divide" , SHAPE_DIVIDE);
   ("shape_conquer" , SHAPE_CONQUER);
   ("shape_lfp" , SHAPE_LFP);
   ("shape_rec" , SHAPE_REC);
   ("shape_split_base", SHAPE_SPLIT_BASE);
   ("pred_elim_hd_node", PRED_ELIM_HEAD);
   ("pred_elim_tl_node", PRED_ELIM_TAIL);
   ("pred_unify_disj", PRED_UNIFY_DISJ);
   ("pred_elim_useless", PRED_ELIM_USELESS);
   ("pred_reuse", PRED_REUSE);
   ("pred_unfold", PRED_UNFOLD);
   ("pred_reuse_subs", PRED_REUSE_SUBS);
   ("shape_extract", SHAPE_EXTRACT);
   ("shape_add_dangling", SHAPE_ADD_DANGLING);
   ("shape_unfold", SHAPE_UNFOLD);
   ("shape_param_dangling", SHAPE_PARAM_DANGLING);
   ("shape_simplify", SHAPE_SIMPLIFY);
   ("shape_merge", SHAPE_MERGE);
   ("shape_trans_to_view", SHAPE_TRANS_TO_VIEW);
   ("shape_derive_pre", SHAPE_DERIVE_PRE);
   ("shape_derive_post", SHAPE_DERIVE_POST);
   ("shape_derive_view", SHAPE_DERIVE_VIEW);
   ("shape_extends_view", SHAPE_EXTN_VIEW);
   ("shape_normalize", SHAPE_NORMALIZE);
   ("data_mark_rec", DATA_MARK_REC);
   ("Declare_Dangling", SHAPE_DECL_DANG);
   ("Declare_Unknown", SHAPE_DECL_UNKNOWN);
   ("shape_strengthen_conseq", SHAPE_STRENGTHEN_CONSEQ );
   ("shape_weaken_ante", SHAPE_WEAKEN_ANTE );
   ("infer_exact", INFER_EXACT);
   ("infer_inexact", INFER_INEXACT);
   ("relation_infer", REL_INFER);
   ("capture_residue", CAPTURERESIDUE);
   ("class", CLASS);
   (* ("coercion", COERCION); *)
   ("compose", COMPOSE);
   ("combine", COMBINE);
   ("const", CONST);
   ("continue", CONTINUE);
   ("data", DATA);
   ("debug", DDEBUG);
   ("diff", DIFF);
   ("dynamic", DYNAMIC);
   ("else", ELSE_TT);
   ("emp", EMPTY);
   ("ensures", ENSURES);
   ("ensures_exact", ENSURES_EXACT);
   ("ensures_inexact", ENSURES_INEXACT);
   ("enum", ENUM);
   (* ("ex", EXISTS); *)
   ("exists", EXISTS);
   ("extends", EXTENDS);
   (* ("extends_rec", EXTENDS_REC); *)
   ("expect_infer", EXPECT_INFER);
   ("false", FALSE);
   ("finalizes", FINALIZE);
   ("finally", FINALLY);
   ("float", FLOAT);
   ("forall", FORALL);
   ("ranking", FUNC);
   ("global",GLOBAL);
   ("logical", LOGICAL);
   ("head",HEAD);
   ("HeapPred", HP);
   ("PostPred", HPPOST);
   ("ho_pred",HPRED);
   ("htrue", HTRUE);
   ("if", IF);
   ("in", IN_T);
   ("infer", INFER);
   ("inline", INLINE); (* An Hoa [22/08/2011] : add inline keyword *)
   ("inlist", INLIST);
   ("int", INT);
   ("char", INT);
   ("INFint", INFINT_TYPE);
   ("intersect", INTERSECT);
   ("inv", INV);
   ("inv_exact", INV_EXACT);
   ("inv_sat", INV_SAT);
   ("BG", BG);
   ("inv_lock", INVLOCK);
   ("joinpred", JOIN); (*Changed by 28/12/2011*)
   ( "rlemma",RLEMMA);
   ("lemma", LEMMA TLEM);
   ("lemma_prop", LEMMA TLEM_PROP);
   ("lemma_split", LEMMA TLEM_SPLIT);
   ("lemma_test", LEMMA TLEM_TEST);
   ("lemma_test_new", LEMMA TLEM_TEST_NEW);
   ("lemma_unsafe", LEMMA TLEM_UNSAFE);
   ("lemma_safe", LEMMA TLEM_SAFE);
   ("lemma_infer", LEMMA TLEM_INFER);
   ("lemma_infer_pred", LEMMA TLEM_INFER_PRED);
   (* ("lemma_exact", LEMMA (\* true *\)); *)
   ("len", LENGTH);
   ("let", LET);
   ("max", MAX);
   ("min", MIN);
   ("new", NEW);
   ("notin", NOTIN);
   ("notinlist", NOTINLIST);
   ("null", NULL);
   ("nil", NULL);
   ("off", OFF);
   ("on", ON);
   ("or", ORWORD);
   ("and", ANDWORD);
   ("macro",PMACRO);
   ("perm",PERM);
   ("pred", PRED);
   ("spec", SPEC);
   ("pred_prim", PRED_PRIM);
   ("pred_extn", PRED_EXT);
   ("hip_include", HIP_INCLUDE);
   ("pred_split", PRED_SPLIT);
   ("pred_norm_disj", PRED_NORM_DISJ);
   ("pred_spec", PRED_SPEC);
   ("pred_norm_seg", PRED_NORM_SEG);
   ("print", PRINT);
   ("print_lemmas", PRINT_LEMMAS);
   ("mem", MEM);
   ("memE", MEME);
   ("dprint", DPRINT);
   ("sleek_compare", CMP);
   ("raise", RAISE);
   ("relation", REL);
   ("requires", REQUIRES);
   ("refines", REFINES);
   ("res", RES "res");
   ("rev",REVERSE);
   ("return", RETURN);
   ("self", SELFT "self");
   ("set",SET);
   ("split", SPLIT);
   ("LexVar", LEXVAR);
   ("template", TEMPL);
   ("UIPre", UIPRE);
   ("UIPost", UIPOST);
   ("UTPre", UTPRE);
   ("UTPost", UTPOST);
   ("Term", TERM);
   ("Loop", LOOP);
   ("MayLoop", MAYLOOP);
   (* ("TermU", TERMU); *)
   (* ("TermR", TERMR); *)
   ("subset", SUBSET);
   ("static", STATIC);
   ("tail",TAIL);
   ("then", THEN);
   ("this", THIS "this");
   ("time", DTIME);
   ("throws", THROWS);
   ("to", TO);
   ("true", TRUE);
   ("try", TRY);
   ("unfold", UNFOLD);
   ("union", UNION);
   ("expect", VALIDATE);
   ("Valid", VALID);
   ("Sat", SSAT);
   ("Unsat", SUNSAT);
   ("Fail", FAIL);
   ("Fail_Must", FAIL_MUST);
   ("Fail_May", FAIL_MAY);
   ("void", VOID);
   (*("variance", VARIANCE);*)
   ("while", WHILE);
   ("with", WITH);
   ("XPURE",XPURE);
   (* Template *)
   ("template", TEMPLATE);
   ("template_solve", TEMPL_SOLVE);
   (flow, FLOW flow);
   ("par", PAR);
   (* ("skip", SKIP) *)
  ]
}


  let newline = ('\010' | '\013' | "\013\010")
  let blank = [' ' '\009' '\012']
  let alpha = ['a'-'z' 'A'-'Z' '\223'-'\246' '\248'-'\255' '_']
  let identchar = ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '0'-'9']
  let identseq = alpha identchar* (* An Hoa : a single identifier *)
  let ident = (identseq | identseq ''') ('.' identseq)* (* An Hoa : a {possibly} extended quantifier *)
  let locname = ident
  let not_star_symbolchar = ['$' '!' '%' '&' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~' '\\']
  let symbolchar = '*' | not_star_symbolchar
  let hexa_char = ['0'-'9' 'A'-'F' 'a'-'f']
  let decimal_literal = ['0'-'9'] ['0'-'9' '_']*
  (* let decimal_literal = ['0'-'9'] ['0'-'9']* *)
  let hex_literal = '0' ['x' 'X'] hexa_char ['0'-'9' 'A'-'F' 'a'-'f' '_']*
  let oct_literal = '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
  let bin_literal = '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
  let int_literal = decimal_literal | hex_literal | oct_literal | bin_literal
  let float_literal = ['0'-'9'] ['0'-'9' '_']* ('.') ['0'-'9' '_']+  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)?
  let frac_literal = int_literal ('/') int_literal

rule tokenizer file_name = parse
  | newline                            { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | blank+                                                  { tokenizer file_name lexbuf }
  | int_literal as i
        { try  INT_LITER(int_of_string i, i)
          with Failure _ -> err (Literal_overflow "int") (Loc.of_lexbuf lexbuf) }
  | float_literal as f
        { try  FLOAT_LIT(float_of_string f, f)
          with Failure _ -> err (Literal_overflow "float") (Loc.of_lexbuf lexbuf) }
  (* | frac_literal as f *)
  (*   { try *)
  (*       let div_index = String.index f '/' in *)
  (*       let num = int_of_string (String.sub f 0 div_index) in *)
  (*       let den = int_of_string (String.sub f (div_index + 1) ((String.length f) - (div_index + 1))) in *)
  (*       FRAC_LIT (Frac.make num den, f) *)
  (*     with _ -> err (Literal_overflow "frac") (Loc.of_lexbuf lexbuf) *)
  (*   } *)
  | (int_literal as i) "l"
        { try  INT_LITER(int_of_string i, i) (*can try different converter if needed*)
          with Failure _ -> err (Literal_overflow "int32") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "L"
        { try  INT_LITER(int_of_string i, i) (*can try different converter if needed*)
          with Failure _ -> err (Literal_overflow "int64") (Loc.of_lexbuf lexbuf) }
  | (int_literal as i) "n"
        { try INT_LITER(int_of_string i, i) (*can try different converter if needed*)
          with Failure _ -> err (Literal_overflow "nativeint") (Loc.of_lexbuf lexbuf) }
  | "'\\" (_ as c)
        { err (Illegal_escape (String.make 1 c)) (Loc.of_lexbuf lexbuf)         }
  | "/*" { comment_level := 0; comment file_name lexbuf }
  | "//" { line_comment file_name lexbuf }
  | "/*/"
        { warn Comment_start (Loc.of_lexbuf lexbuf);
          comment_level := 0;
          comment file_name lexbuf}
  | "*/"
        { warn Comment_not_end (Loc.of_lexbuf lexbuf)                           ;
          move_start_p (-1) file_name; STAR                                      }
  | '"'
        { with_curr_loc string file_name;
          let s = buff_contents file_name in STRING (Camlp4.Struct.Token.Eval.string s, s)     }
  | "'" (newline as x) "'"
        { update_loc file_name None 1 false 1; CHAR_LIT (Camlp4.Struct.Token.Eval.char x, x)       }
  | "'" ( [^ '\\' '\010' '\013']
            | '\\' (['\\' '"' 'n' 't' 'b' 'r' ' ' '\'']
                |['0'-'9'] ['0'-'9'] ['0'-'9']
                |'x' hexa_char hexa_char)
          as x) "'"                                { CHAR_LIT (Camlp4.Struct.Token.Eval.char x, x) }
  | "##OPTION " (['0'-'9' 'A'-'Z' 'a'-'z' '-' ' ' '.' '_' '"' ]* as x) {ARGOPTION (Camlp4.Struct.Token.Eval.string x)}
  | "@frac" { PFRAC }
  | "@A" { ACCS }
  | '&' { AND }
  | "&*" { ANDSTAR }
  | "&&" { ANDAND }
  | "U*" { UNIONSTAR }
  | "--@" { STARMINUS }
  | "@" { AT }
  | "@@" { ATAT }
  | "@@[" { ATATSQ }
  | "@I" {IMM}
  | "@L" {LEND}
  | "@A" {ACCS}
  | "@D" { DERV }
  | "@S1" { SPLIT1Ann }
  | "@S2" { SPLIT2Ann }
  | "@M" { MUT }
  | "@S" { SAT }
  (* | "@VAL" {VAL} *)
  | "@C" {PASS_COPY}
  | "@R" {PASS_REF}
  | "ref" {PASS_REF2}
  (* | "@REC" {REC} *)
  | "@NI" {NI}
  | "@RO" {RO}
  | "@pre" { PRE }  (* to be changed *)
  | "@xpre" { XPRE } (* WN : what is this? *)
  | "@post" { POST } (* to be changed *)
  | "@leak" { INFER_AT_CLASSIC }
  | "@classic" { INFER_AT_CLASSIC }
  | "@par" { INFER_AT_PAR }
  | "@term" { INFER_AT_TERM }
  | "@term_wo_post" { INFER_AT_TERM_WO_POST }
  | "@pre_n" { INFER_AT_PRE }
  | "@post_n" { INFER_AT_POST }
  | "@ver_post" { INFER_AT_VER_POST }
  | "@imm_pre" { INFER_IMM_PRE }
  | "@pure_field" { INFER_AT_PURE_FIELD }
  | "@imm_post" { INFER_IMM_POST }
  | "@imm" { INFER_AT_IMM }
  | "@field_imm" { INFER_AT_FIELD_IMM }
  | "@arrvar" { INFER_AT_ARR_AS_VAR }
  | "@shape" { INFER_AT_SHAPE }
  | "@shape_pre" { INFER_AT_SHAPE_PRE }
  | "@shape_post" { INFER_AT_SHAPE_POST }
  | "@shape_prepost" { INFER_AT_SHAPE_PRE_POST }
  | "@error" { INFER_AT_ERROR }
  | "@dis_err" { INFER_AT_DE_EXC }
  | "@err_must" { INFER_AT_ERRMUST }
  | "@pre_must" { INFER_AT_PREMUST }
  | "@err_must_only" { INFER_AT_ERRMUST_ONLY }
  | "@err_may" { INFER_AT_ERRMAY }
  | "@flow" { INFER_AT_FLOW }
  | "@size" { INFER_AT_SIZE }
  | "@ana_ni" { INFER_ANA_NI }
  | "@efa" { INFER_AT_EFA }
  | "@dfa" { INFER_AT_DFA }
  | "termAssume" { TREL_ASSUME }
  | "term_infer" { TERM_INFER }
  | "@xpost" { XPOST }
(*  | "XPURE" {XPURE} *)
  | "@zero" {PZERO}
  | "@full" {PFULL}
  | "@value" {PVALUE}
  | "@lend" { PLEND }
  | "@Split" { SPLITANN } (*Split annotation*)
  | "tup2" { TUP2 } (*pair*)
  (* | "@p_ref" {PREF} *)
  | '^' { CARET }
  | '}' { CBRACE }
  | "|]" {CLIST}
  | ':' { COLON }
  | "::" { COLONCOLON }
  | ":::" { COLONCOLONCOLON }
  | ',' { COMMA }
  | ')' { CPAREN }
  | ']' { CSQUARE }
  | '$' { DOLLAR }
  | "." { DOT }
  | ".." { DOTDOT }
  | "\"" { DOUBLEQUOTE }
  | "\\inf" {INFINITY}
  | "~\\inf" {NEGINFINITY}
  | "=" { EQ }
  | "==" { EQEQ }
  | "==>" { ESCAPE }
  | "<-" { RIGHTARROW }
  | "<->" { EQUIV }
  | '>' { GT }
  | ">=" { GTE }
  | '#' { HASH }
  | "|#|" {REL_GUARD}
  | "->" { LEFTARROW }
  | '<' { LT }
  | "<=" { LTE }
  | "-" { MINUS }
  | "!=" { NEQ }
  | "!" { NOT }
  | '{' { OBRACE }
  | "[|" {OLIST}
  | '(' { OPAREN }
  | "+=" { OP_ADD_ASSIGN }
  | "--" { OP_DEC }
  | "/=" { OP_DIV_ASSIGN }
  | "++" { OP_INC }
  | "%=" { OP_MOD_ASSIGN }
  | "*=" { OP_MULT_ASSIGN }
  | "-=" { OP_SUB_ASSIGN }
  | '|' { OR }
  | "||" { OROR }
  | "|-" { (* (print_string "der\n"; *)DERIVE }
  | "-|-" { EQV }
  | "-->" { CONSTR }
  (* | "<#" { TOPAREN } *) (* replaced by `LT;`HASH. inline\data-holes.lsk. examples/fracperm/thread/thrd1.slk*)
  (* | "#>" { TCPAREN } (\*Open and close paren for thread heap*\) *) (* replaced by `HASH;`GT*)
  (* | "-%" { IN_RFLOW }  *)
  (* | "+%" { OUT_RFLOW } *)
  | '[' { OSQUARE }
  | '%' { PERCENT }
  | '+' { PLUS }
  | '\'' { PRIME }
  | ';' { SEMICOLON }
  | '*' { STAR }
  | "<:" { SUBANN }
  | '/' { DIV }
  | ident as idstr
	  {
		if idstr = "_" then
		  IDENTIFIER ("Anon" ^ fresh_trailer ())
		  (* IDENTIFIER ("Anon" ^ fresh_trailer ()) *)
		else if idstr = "java" then begin
      store file_name; JAVA (parse_nested java file_name)
		end else
		  try Hashtbl.find sleek_keywords idstr
		  with | _ -> IDENTIFIER idstr
	  }
  | eof
      { let pos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { pos with pos_bol  = pos.pos_bol  + 1 ;
                                        pos_cnum = pos.pos_cnum + 1 }; EOF      }
  | _ as c                 { err (Illegal_character c) (Loc.of_lexbuf lexbuf) }

(* search for the first open brace following java keyword *)
and java file_name = parse
  | "{"   { store file_name; with_curr_loc java file_name; parse java file_name }
  | "}"                                                         {store file_name}
  | ident                                          { store_parse java file_name }
  | eof                                  { err Unterminated_java (loc file_name)}
  | newline    { update_loc file_name None 1 false 0; store_parse java file_name}
  | _                                              { store_parse java file_name }

and comment file_name = parse
  | "*/" {
	  if !comment_level = 0 then
		tokenizer file_name lexbuf
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end	}
  | "/*" {
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf}
  | newline { update_loc file_name None 1 false 0; comment file_name lexbuf }
  | _  { comment file_name lexbuf }

and line_comment file_name = parse
  | newline
  | eof { update_loc file_name None 1 false 0; tokenizer file_name lexbuf }
  | _ { line_comment file_name lexbuf }


and string c = parse
      '"'                                                       { set_start_p c }
    | '\\' newline ([' ' '\t'] * as space)
        { update_loc c None 1 false (String.length space);
          store_parse string c                                                  }
    | '\\' ['\\' '"' 'n' 't' 'b' 'r' ' ' '\'']           { store_parse string c }
    | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']                 { store_parse string c }
    | '\\' 'x' hexa_char hexa_char                       { store_parse string c }
    | '\\' (_ as x)
        { if is_in_comment c
          then store_parse string c
          else begin
            warn (Illegal_escape (String.make 1 x)) (Loc.of_lexbuf lexbuf);
            store_parse string c
          end }
    | newline
      { update_loc c None 1 false 0; store_parse string c                       }
    | eof                                     { err Unterminated_string (loc c) }
    | _                                                  { store_parse string c }


and preprocess file_name = parse
  | "import"
      {
		(* processing import *)
		let _ = rip_ws lexbuf in
		let tmp_file_name = get_file_name lexbuf in
		let f1 = String.sub tmp_file_name 1 (String.length tmp_file_name - 2) in
		let in_file = open_in f1 in
		let cont = ref true in
		let in_cont = Buffer.create 1024 in
		  while !cont do
			try
			  let line = input_line in_file in
				Buffer.add_string in_cont (line ^ "\n")
			with
			  | End_of_file -> cont := false
		  done;
		  output_string file_name (Buffer.contents in_cont);
		  preprocess file_name lexbuf
      }
  | _ as c
      { (* other character, just copy it over *)
		output_char file_name c;
		preprocess file_name lexbuf
      }
  | eof { EOF }

and rip_ws = parse
  | (' ' | '\t')+ as ws { ws }
  | _  { print_string "There must be whitespace after import directive\n"; exit (-1) }

and get_file_name = parse
  | '\"'([^ '\n' '\"'])+'\"' as fn { fn }
  | _ { print_string "file name following import must be enclosed in double quotes\n"; exit (-1) }

{

  let lexing_store s buff max =
    let rec self n s =
      if n >= max then n
      else
        match Stream.peek s with
        | Some x ->
            Stream.junk s;
            buff.[n] <- x;
            succ n
        | _ -> n
    in
    self 0 s

  let from_context c =
    let next _ =
      let tok = with_curr_loc tokenizer c in
      let loc = Loc.of_lexbuf c.lexbuf in
      Some ((tok, loc))
    in Stream.from next

  let from_lexbuf lb =
    let c = { (default_context lb) with  loc = Loc.of_lexbuf lb}
    in from_context c

  let setup_loc lb loc =
    let start_pos = Loc.start_pos loc in
    lb.lex_abs_pos <- start_pos.pos_cnum;
    lb.lex_curr_p  <- start_pos

  let from_string loc str =
    let lb = Lexing.from_string str in
    setup_loc lb loc;
    from_lexbuf lb

  let from_stream loc strm =
    let lb = Lexing.from_function (lexing_store strm) in
    setup_loc lb loc;
    from_lexbuf lb

  let mk () loc strm = from_stream loc strm
end
}
