# 1 "slexer.mll"
 
  open Globals
  open Sparser

  let comment_level = ref (0 : int)

  let java_bcount = ref (0 : int)
  let java_code = Buffer.create 100

  let incr_linenum file_name lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- 
	{ pos with
	    Lexing.pos_fname = file_name;
	    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
	    Lexing.pos_bol = pos.Lexing.pos_cnum;
	}

  let print_error lexbuf msg =
	let pos = lexbuf.Lexing.lex_curr_p in
	  Error.report_error {Error.error_loc = pos;
						  Error.error_text = msg}

  let keywords = Hashtbl.create 100
  let _ = List.map (fun (k, t) -> Hashtbl.add keywords k t)
	[("assert", ASSERT);
	 ("assume", ASSUME);
	 ("bind", BIND);
	 ("bool", BOOL);
	 ("break", BREAK);
	 ("by", BY);
	 ("checkentail", CHECKENTAIL);
	 ("capture_residue", CAPTURERESIDUE);
	 ("class", CLASS);
	 ("coercion", COERCION);
	 ("compose", COMPOSE);
	 ("conseq", CONSEQ);
	 ("const", CONST);
	 ("continue", CONTINUE);
	 ("data", DATA);
	 ("debug", DDEBUG);
	 ("diff", DIFF);
	 ("dynamic", DYNAMIC);
	 ("else", ELSE);
	 ("ensures", ENSURES);
	 ("enum", ENUM);
	 ("ex", EXISTS);
	 ("exists", EXISTS);
	 ("extends", EXTENDS);
	 ("false", FALSE);
	 ("float", FLOAT);
	 ("fold", FOLD);
	 ("forall", FORALL);
	 ("if", IF);
	 ("implies", IMPLIES);
	 ("import", IMPORT);
	 ("in", IN);
	 ("int", INT);
	 ("intersect", INTERSECT);
	 ("inv", INV);
	 ("lemma", LEMMA);
	 ("let", LET);
	 ("max", MAX);
	 ("min", MIN);
	 ("bagmax", BAGMAX);
	 ("bagmin", BAGMIN);
	 ("new", NEW);
	 ("notin", NOTIN);
	 ("null", NULL);
	 ("off", OFF);
	 ("on", ON);
	 ("or", ORWORD);
	 ("pred", PRED);
	 ("print", PRINT);
	 ("ref", REF);
	 ("requires", REQUIRES);
	 ("res", RES "res");
	 ("return", RETURN);
	 ("self", SELF "self");
	 ("split", SPLIT);
	 ("subset", SUBSET);
	 ("static", STATIC);
	 ("then", THEN);
	 ("this", THIS "this");
	 ("to", TO);
	 ("true", TRUE);
	 ("unfold", UNFOLD);
	 ("union", UNION);
	 ("view", VIEW);
	 ("void", VOID);
	 ("where", WHERE);
	 ("while", WHILE)]

# 96 "slexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\202\255\001\000\205\255\206\255\078\000\155\000\211\255\
    \212\255\215\255\018\000\031\000\033\000\159\000\226\255\227\255\
    \035\000\168\000\235\255\075\000\170\000\076\000\242\255\184\000\
    \244\255\245\255\246\255\247\255\081\000\250\255\251\255\102\000\
    \181\000\223\255\254\255\255\255\252\255\248\255\195\000\234\255\
    \240\255\231\255\079\000\238\255\236\255\219\255\224\255\233\255\
    \229\255\222\255\225\255\221\255\220\255\216\255\217\255\209\000\
    \203\255\244\000\253\255\159\000\002\000\001\001\004\000\128\000\
    \124\000\012\000\005\000\069\000\105\000\104\000\106\000\104\000\
    \103\000\245\000\246\000\187\000\003\001\005\001";
  Lexing.lex_backtrk = 
   "\255\255\255\255\051\000\255\255\255\255\048\000\046\000\255\255\
    \255\255\255\255\037\000\045\000\041\000\042\000\255\255\255\255\
    \027\000\025\000\255\255\018\000\023\000\014\000\255\255\012\000\
    \255\255\255\255\255\255\255\255\006\000\255\255\255\255\002\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\047\000\255\255\
    \255\255\255\255\016\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\003\000\255\255\003\000\005\000\
    \005\000\255\255\000\000\255\255\001\000\255\255\255\255\255\255\
    \255\255\255\255\000\000\255\255\001\000\255\255";
  Lexing.lex_default = 
   "\255\255\000\000\255\255\000\000\000\000\255\255\255\255\000\000\
    \000\000\000\000\255\255\255\255\255\255\255\255\000\000\000\000\
    \255\255\255\255\000\000\255\255\255\255\255\255\000\000\255\255\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \000\000\058\000\000\000\029\000\255\255\029\000\255\255\255\255\
    \255\255\034\000\255\255\034\000\255\255\255\255\255\255\255\255\
    \255\255\034\000\255\255\034\000\077\000\077\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\004\000\003\000\056\000\030\000\002\000\030\000\035\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\035\000\000\000\
    \000\000\066\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \004\000\016\000\022\000\018\000\024\000\012\000\031\000\008\000\
    \014\000\026\000\011\000\013\000\027\000\017\000\023\000\032\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\028\000\007\000\020\000\021\000\019\000\053\000\
    \030\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\009\000\052\000\025\000\051\000\005\000\
    \048\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\015\000\010\000\029\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \044\000\040\000\039\000\037\000\036\000\043\000\054\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\058\000\034\000\035\000\060\000\005\000\068\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\055\000\049\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\046\000\069\000\042\000\
    \070\000\071\000\072\000\035\000\050\000\076\000\000\000\035\000\
    \000\000\000\000\000\000\000\000\034\000\045\000\047\000\041\000\
    \038\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\033\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\038\000\038\000\034\000\074\000\074\000\
    \001\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\058\000\255\255\255\255\062\000\255\255\
    \000\000\000\000\000\000\000\000\034\000\074\000\074\000\000\000\
    \000\000\000\000\034\000\000\000\035\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\000\000\035\000\
    \000\000\000\000\000\000\064\000\000\000\000\000\000\000\000\000\
    \063\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\058\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\035\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\255\255\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\255\255\000\000\255\255";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\002\000\060\000\000\000\062\000\066\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\065\000\255\255\
    \255\255\065\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\010\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\011\000\000\000\012\000\000\000\
    \016\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \019\000\021\000\021\000\028\000\031\000\042\000\010\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\059\000\063\000\064\000\059\000\005\000\067\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\006\000\013\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\017\000\068\000\020\000\
    \069\000\070\000\071\000\072\000\013\000\075\000\255\255\032\000\
    \255\255\255\255\255\255\255\255\032\000\017\000\017\000\020\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\032\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\038\000\038\000\057\000\073\000\074\000\
    \000\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\061\000\065\000\076\000\061\000\077\000\
    \255\255\255\255\255\255\255\255\057\000\073\000\074\000\255\255\
    \255\255\255\255\059\000\255\255\059\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\076\000\255\255\077\000\
    \255\255\255\255\255\255\061\000\255\255\255\255\255\255\255\255\
    \061\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\067\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\057\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\059\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\075\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\057\000\073\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\061\000\255\255\076\000\255\255\077\000";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec tokenizer file_name lexbuf =
    __ocaml_lex_tokenizer_rec file_name lexbuf 0
and __ocaml_lex_tokenizer_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 102 "slexer.mll"
         ( 
	  comment_level := 0;
	  comment file_name lexbuf 
	)
# 287 "slexer.ml"

  | 1 ->
# 106 "slexer.mll"
         ( line_comment file_name lexbuf )
# 292 "slexer.ml"

  | 2 ->
# 107 "slexer.mll"
        ( AND )
# 297 "slexer.ml"

  | 3 ->
# 108 "slexer.mll"
         ( ANDAND )
# 302 "slexer.ml"

  | 4 ->
# 109 "slexer.mll"
        ( AT )
# 307 "slexer.ml"

  | 5 ->
# 110 "slexer.mll"
        ( CBRACE )
# 312 "slexer.ml"

  | 6 ->
# 111 "slexer.mll"
        ( COLON )
# 317 "slexer.ml"

  | 7 ->
# 112 "slexer.mll"
         ( COLONCOLON )
# 322 "slexer.ml"

  | 8 ->
# 113 "slexer.mll"
        ( COMMA )
# 327 "slexer.ml"

  | 9 ->
# 114 "slexer.mll"
        ( CPAREN )
# 332 "slexer.ml"

  | 10 ->
# 115 "slexer.mll"
        ( CSQUARE )
# 337 "slexer.ml"

  | 11 ->
# 116 "slexer.mll"
        ( DOLLAR )
# 342 "slexer.ml"

  | 12 ->
# 117 "slexer.mll"
        ( DOT )
# 347 "slexer.ml"

  | 13 ->
# 118 "slexer.mll"
         ( DOUBLEQUOTE )
# 352 "slexer.ml"

  | 14 ->
# 119 "slexer.mll"
        ( EQ )
# 357 "slexer.ml"

  | 15 ->
# 120 "slexer.mll"
         ( EQEQ )
# 362 "slexer.ml"

  | 16 ->
# 121 "slexer.mll"
         ( RIGHTARROW )
# 367 "slexer.ml"

  | 17 ->
# 122 "slexer.mll"
          ( EQUIV )
# 372 "slexer.ml"

  | 18 ->
# 123 "slexer.mll"
        ( GT )
# 377 "slexer.ml"

  | 19 ->
# 124 "slexer.mll"
         ( GTE )
# 382 "slexer.ml"

  | 20 ->
# 125 "slexer.mll"
        ( HASH )
# 387 "slexer.ml"

  | 21 ->
# 126 "slexer.mll"
         ( IMPLY )
# 392 "slexer.ml"

  | 22 ->
# 127 "slexer.mll"
         ( LEFTARROW )
# 397 "slexer.ml"

  | 23 ->
# 128 "slexer.mll"
        ( LT )
# 402 "slexer.ml"

  | 24 ->
# 129 "slexer.mll"
         ( LTE )
# 407 "slexer.ml"

  | 25 ->
# 130 "slexer.mll"
        ( MINUS )
# 412 "slexer.ml"

  | 26 ->
# 131 "slexer.mll"
         ( NEQ )
# 417 "slexer.ml"

  | 27 ->
# 132 "slexer.mll"
        ( NOT )
# 422 "slexer.ml"

  | 28 ->
# 133 "slexer.mll"
        ( OBRACE )
# 427 "slexer.ml"

  | 29 ->
# 134 "slexer.mll"
        ( OPAREN )
# 432 "slexer.ml"

  | 30 ->
# 135 "slexer.mll"
         ( OP_ADD_ASSIGN )
# 437 "slexer.ml"

  | 31 ->
# 136 "slexer.mll"
         ( OP_DEC )
# 442 "slexer.ml"

  | 32 ->
# 137 "slexer.mll"
         ( OP_DIV_ASSIGN )
# 447 "slexer.ml"

  | 33 ->
# 138 "slexer.mll"
         ( OP_INC )
# 452 "slexer.ml"

  | 34 ->
# 139 "slexer.mll"
         ( OP_MOD_ASSIGN )
# 457 "slexer.ml"

  | 35 ->
# 140 "slexer.mll"
         ( OP_MULT_ASSIGN )
# 462 "slexer.ml"

  | 36 ->
# 141 "slexer.mll"
         ( OP_SUB_ASSIGN )
# 467 "slexer.ml"

  | 37 ->
# 142 "slexer.mll"
        ( OR )
# 472 "slexer.ml"

  | 38 ->
# 143 "slexer.mll"
         ( OROR )
# 477 "slexer.ml"

  | 39 ->
# 144 "slexer.mll"
         ( DERIVE )
# 482 "slexer.ml"

  | 40 ->
# 145 "slexer.mll"
        ( OSQUARE )
# 487 "slexer.ml"

  | 41 ->
# 146 "slexer.mll"
        ( PERCENT )
# 492 "slexer.ml"

  | 42 ->
# 147 "slexer.mll"
        ( PLUS )
# 497 "slexer.ml"

  | 43 ->
# 148 "slexer.mll"
         ( PRIME )
# 502 "slexer.ml"

  | 44 ->
# 149 "slexer.mll"
        ( SEMICOLON )
# 507 "slexer.ml"

  | 45 ->
# 150 "slexer.mll"
        ( STAR )
# 512 "slexer.ml"

  | 46 ->

  let numstr = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 151 "slexer.mll"
                     ( LITERAL_INTEGER (int_of_string numstr) )
# 519 "slexer.ml"

  | 47 ->

  let numstr = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 152 "slexer.mll"
                   ( LITERAL_FLOAT (float_of_string numstr) )
# 526 "slexer.ml"

  | 48 ->

  let idstr = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 154 "slexer.mll"
   (
		if idstr = "_" then
		  IDENTIFIER ("Anon_" ^ fresh_name ())
		else if idstr = "java" then begin
		  pre_java file_name lexbuf (* search for the first opening brace *)
		end else
		  try Hashtbl.find keywords idstr
		  with | _ -> IDENTIFIER idstr
	  )
# 541 "slexer.ml"

  | 49 ->
# 163 "slexer.mll"
               ( tokenizer file_name lexbuf )
# 546 "slexer.ml"

  | 50 ->
# 164 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 551 "slexer.ml"

  | 51 ->
# 165 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 556 "slexer.ml"

  | 52 ->
# 166 "slexer.mll"
           ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 561 "slexer.ml"

  | 53 ->
# 167 "slexer.mll"
        ( EOF )
# 566 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_tokenizer_rec file_name lexbuf __ocaml_lex_state

and pre_java file_name lexbuf =
    __ocaml_lex_pre_java_rec file_name lexbuf 57
and __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 171 "slexer.mll"
        (
	  java_bcount := 0;
	  Buffer.clear java_code;
	  java file_name lexbuf
	)
# 581 "slexer.ml"

  | 1 ->
# 176 "slexer.mll"
               ( pre_java file_name lexbuf )
# 586 "slexer.ml"

  | 2 ->
# 177 "slexer.mll"
      ( print_error lexbuf "java keyword must be followed by Java code enclosed in {}" )
# 591 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state

and java file_name lexbuf =
    __ocaml_lex_java_rec file_name lexbuf 59
and __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 180 "slexer.mll"
        (
	  if !java_bcount = 0 then
		JAVA (Buffer.contents java_code)
	  else begin
		java_bcount := !java_bcount - 1;
		Buffer.add_char java_code '}';
		java file_name lexbuf
	  end
	)
# 610 "slexer.ml"

  | 1 ->
# 189 "slexer.mll"
        (
	  java_bcount := !java_bcount + 1;
	  Buffer.add_char java_code '{';
	  java file_name lexbuf
	)
# 619 "slexer.ml"

  | 2 ->
# 194 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\n'; 
	  java file_name lexbuf 
	)
# 628 "slexer.ml"

  | 3 ->
# 199 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\r'; 
	  java file_name lexbuf 
	)
# 637 "slexer.ml"

  | 4 ->
# 204 "slexer.mll"
           (
	  incr_linenum file_name lexbuf; 
	  Buffer.add_string java_code "\r\n";
	  java file_name lexbuf 
	)
# 646 "slexer.ml"

  | 5 ->

  let c = Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 209 "slexer.mll"
            ( 
	  Buffer.add_char java_code c;
	  java file_name lexbuf 
	)
# 656 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state

and comment file_name lexbuf =
    __ocaml_lex_comment_rec file_name lexbuf 61
and __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 216 "slexer.mll"
         ( 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end
	)
# 674 "slexer.ml"

  | 1 ->
# 224 "slexer.mll"
         (
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf
	)
# 682 "slexer.ml"

  | 2 ->
# 228 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 687 "slexer.ml"

  | 3 ->
# 229 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 692 "slexer.ml"

  | 4 ->
# 230 "slexer.mll"
           ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 697 "slexer.ml"

  | 5 ->
# 231 "slexer.mll"
       ( comment file_name lexbuf )
# 702 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state

and line_comment file_name lexbuf =
    __ocaml_lex_line_comment_rec file_name lexbuf 65
and __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 234 "slexer.mll"
                         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 713 "slexer.ml"

  | 1 ->
# 235 "slexer.mll"
      ( line_comment file_name lexbuf )
# 718 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state

and preprocess pfile lexbuf =
    __ocaml_lex_preprocess_rec pfile lexbuf 67
and __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 239 "slexer.mll"
      (
		(* processing import *)
		let _ = rip_ws lexbuf in
		let tmp_file_name = get_file_name lexbuf in
		let file_name = String.sub tmp_file_name 1 (String.length tmp_file_name - 2) in
		let in_file = open_in file_name in
		let cont = ref true in
		let in_cont = Buffer.create 1024 in
		  while !cont do
			try
			  let line = input_line in_file in
				Buffer.add_string in_cont (line ^ "\n")
			with
			  | End_of_file -> cont := false
		  done;
		  output_string pfile (Buffer.contents in_cont);
		  preprocess pfile lexbuf
      )
# 746 "slexer.ml"

  | 1 ->

  let c = Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 258 "slexer.mll"
      ( (* other character, just copy it over *)
		output_char pfile c;
		preprocess pfile lexbuf
		  
      )
# 757 "slexer.ml"

  | 2 ->
# 263 "slexer.mll"
        (  )
# 762 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state

and rip_ws lexbuf =
    __ocaml_lex_rip_ws_rec lexbuf 73
and __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let ws = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 266 "slexer.mll"
                        ( ws )
# 775 "slexer.ml"

  | 1 ->
# 267 "slexer.mll"
       ( print_string "There must be whitespace after import directive\n"; exit (-1) )
# 780 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state

and get_file_name lexbuf =
    __ocaml_lex_get_file_name_rec lexbuf 75
and __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let fn = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 270 "slexer.mll"
                                   ( fn )
# 793 "slexer.ml"

  | 1 ->
# 271 "slexer.mll"
      ( print_string "file name following import must be enclosed in double quotes\n"; exit (-1) )
# 798 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state

;;

