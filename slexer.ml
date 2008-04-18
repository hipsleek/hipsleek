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

# 95 "slexer.ml"
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
# 101 "slexer.mll"
         ( 
	  comment_level := 0;
	  comment file_name lexbuf 
	)
# 286 "slexer.ml"

  | 1 ->
# 105 "slexer.mll"
         ( line_comment file_name lexbuf )
# 291 "slexer.ml"

  | 2 ->
# 106 "slexer.mll"
        ( AND )
# 296 "slexer.ml"

  | 3 ->
# 107 "slexer.mll"
         ( ANDAND )
# 301 "slexer.ml"

  | 4 ->
# 108 "slexer.mll"
        ( AT )
# 306 "slexer.ml"

  | 5 ->
# 109 "slexer.mll"
        ( CBRACE )
# 311 "slexer.ml"

  | 6 ->
# 110 "slexer.mll"
        ( COLON )
# 316 "slexer.ml"

  | 7 ->
# 111 "slexer.mll"
         ( COLONCOLON )
# 321 "slexer.ml"

  | 8 ->
# 112 "slexer.mll"
        ( COMMA )
# 326 "slexer.ml"

  | 9 ->
# 113 "slexer.mll"
        ( CPAREN )
# 331 "slexer.ml"

  | 10 ->
# 114 "slexer.mll"
        ( CSQUARE )
# 336 "slexer.ml"

  | 11 ->
# 115 "slexer.mll"
        ( DOLLAR )
# 341 "slexer.ml"

  | 12 ->
# 116 "slexer.mll"
        ( DOT )
# 346 "slexer.ml"

  | 13 ->
# 117 "slexer.mll"
         ( DOUBLEQUOTE )
# 351 "slexer.ml"

  | 14 ->
# 118 "slexer.mll"
        ( EQ )
# 356 "slexer.ml"

  | 15 ->
# 119 "slexer.mll"
         ( EQEQ )
# 361 "slexer.ml"

  | 16 ->
# 120 "slexer.mll"
         ( RIGHTARROW )
# 366 "slexer.ml"

  | 17 ->
# 121 "slexer.mll"
          ( EQUIV )
# 371 "slexer.ml"

  | 18 ->
# 122 "slexer.mll"
        ( GT )
# 376 "slexer.ml"

  | 19 ->
# 123 "slexer.mll"
         ( GTE )
# 381 "slexer.ml"

  | 20 ->
# 124 "slexer.mll"
        ( HASH )
# 386 "slexer.ml"

  | 21 ->
# 125 "slexer.mll"
         ( IMPLY )
# 391 "slexer.ml"

  | 22 ->
# 126 "slexer.mll"
         ( LEFTARROW )
# 396 "slexer.ml"

  | 23 ->
# 127 "slexer.mll"
        ( LT )
# 401 "slexer.ml"

  | 24 ->
# 128 "slexer.mll"
         ( LTE )
# 406 "slexer.ml"

  | 25 ->
# 129 "slexer.mll"
        ( MINUS )
# 411 "slexer.ml"

  | 26 ->
# 130 "slexer.mll"
         ( NEQ )
# 416 "slexer.ml"

  | 27 ->
# 131 "slexer.mll"
        ( NOT )
# 421 "slexer.ml"

  | 28 ->
# 132 "slexer.mll"
        ( OBRACE )
# 426 "slexer.ml"

  | 29 ->
# 133 "slexer.mll"
        ( OPAREN )
# 431 "slexer.ml"

  | 30 ->
# 134 "slexer.mll"
         ( OP_ADD_ASSIGN )
# 436 "slexer.ml"

  | 31 ->
# 135 "slexer.mll"
         ( OP_DEC )
# 441 "slexer.ml"

  | 32 ->
# 136 "slexer.mll"
         ( OP_DIV_ASSIGN )
# 446 "slexer.ml"

  | 33 ->
# 137 "slexer.mll"
         ( OP_INC )
# 451 "slexer.ml"

  | 34 ->
# 138 "slexer.mll"
         ( OP_MOD_ASSIGN )
# 456 "slexer.ml"

  | 35 ->
# 139 "slexer.mll"
         ( OP_MULT_ASSIGN )
# 461 "slexer.ml"

  | 36 ->
# 140 "slexer.mll"
         ( OP_SUB_ASSIGN )
# 466 "slexer.ml"

  | 37 ->
# 141 "slexer.mll"
        ( OR )
# 471 "slexer.ml"

  | 38 ->
# 142 "slexer.mll"
         ( OROR )
# 476 "slexer.ml"

  | 39 ->
# 143 "slexer.mll"
         ( DERIVE )
# 481 "slexer.ml"

  | 40 ->
# 144 "slexer.mll"
        ( OSQUARE )
# 486 "slexer.ml"

  | 41 ->
# 145 "slexer.mll"
        ( PERCENT )
# 491 "slexer.ml"

  | 42 ->
# 146 "slexer.mll"
        ( PLUS )
# 496 "slexer.ml"

  | 43 ->
# 147 "slexer.mll"
         ( PRIME )
# 501 "slexer.ml"

  | 44 ->
# 148 "slexer.mll"
        ( SEMICOLON )
# 506 "slexer.ml"

  | 45 ->
# 149 "slexer.mll"
        ( STAR )
# 511 "slexer.ml"

  | 46 ->

  let numstr = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 150 "slexer.mll"
                     ( LITERAL_INTEGER (int_of_string numstr) )
# 518 "slexer.ml"

  | 47 ->

  let numstr = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 151 "slexer.mll"
                   ( LITERAL_FLOAT (float_of_string numstr) )
# 525 "slexer.ml"

  | 48 ->

  let idstr = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 153 "slexer.mll"
   (
		if idstr = "_" then
		  IDENTIFIER ("Anon_" ^ fresh_name ())
		else if idstr = "java" then begin
		  pre_java file_name lexbuf (* search for the first opening brace *)
		end else
		  try Hashtbl.find keywords idstr
		  with | _ -> IDENTIFIER idstr
	  )
# 540 "slexer.ml"

  | 49 ->
# 162 "slexer.mll"
               ( tokenizer file_name lexbuf )
# 545 "slexer.ml"

  | 50 ->
# 163 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 550 "slexer.ml"

  | 51 ->
# 164 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 555 "slexer.ml"

  | 52 ->
# 165 "slexer.mll"
           ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 560 "slexer.ml"

  | 53 ->
# 166 "slexer.mll"
        ( EOF )
# 565 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_tokenizer_rec file_name lexbuf __ocaml_lex_state

and pre_java file_name lexbuf =
    __ocaml_lex_pre_java_rec file_name lexbuf 57
and __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 170 "slexer.mll"
        (
	  java_bcount := 0;
	  Buffer.clear java_code;
	  java file_name lexbuf
	)
# 580 "slexer.ml"

  | 1 ->
# 175 "slexer.mll"
               ( pre_java file_name lexbuf )
# 585 "slexer.ml"

  | 2 ->
# 176 "slexer.mll"
      ( print_error lexbuf "java keyword must be followed by Java code enclosed in {}" )
# 590 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state

and java file_name lexbuf =
    __ocaml_lex_java_rec file_name lexbuf 59
and __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 179 "slexer.mll"
        (
	  if !java_bcount = 0 then
		JAVA (Buffer.contents java_code)
	  else begin
		java_bcount := !java_bcount - 1;
		Buffer.add_char java_code '}';
		java file_name lexbuf
	  end
	)
# 609 "slexer.ml"

  | 1 ->
# 188 "slexer.mll"
        (
	  java_bcount := !java_bcount + 1;
	  Buffer.add_char java_code '{';
	  java file_name lexbuf
	)
# 618 "slexer.ml"

  | 2 ->
# 193 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\n'; 
	  java file_name lexbuf 
	)
# 627 "slexer.ml"

  | 3 ->
# 198 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\r'; 
	  java file_name lexbuf 
	)
# 636 "slexer.ml"

  | 4 ->
# 203 "slexer.mll"
           (
	  incr_linenum file_name lexbuf; 
	  Buffer.add_string java_code "\r\n";
	  java file_name lexbuf 
	)
# 645 "slexer.ml"

  | 5 ->

  let c = Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 208 "slexer.mll"
            ( 
	  Buffer.add_char java_code c;
	  java file_name lexbuf 
	)
# 655 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state

and comment file_name lexbuf =
    __ocaml_lex_comment_rec file_name lexbuf 61
and __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 215 "slexer.mll"
         ( 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end
	)
# 673 "slexer.ml"

  | 1 ->
# 223 "slexer.mll"
         (
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf
	)
# 681 "slexer.ml"

  | 2 ->
# 227 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 686 "slexer.ml"

  | 3 ->
# 228 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 691 "slexer.ml"

  | 4 ->
# 229 "slexer.mll"
           ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 696 "slexer.ml"

  | 5 ->
# 230 "slexer.mll"
       ( comment file_name lexbuf )
# 701 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state

and line_comment file_name lexbuf =
    __ocaml_lex_line_comment_rec file_name lexbuf 65
and __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 233 "slexer.mll"
                         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 712 "slexer.ml"

  | 1 ->
# 234 "slexer.mll"
      ( line_comment file_name lexbuf )
# 717 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state

and preprocess pfile lexbuf =
    __ocaml_lex_preprocess_rec pfile lexbuf 67
and __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 238 "slexer.mll"
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
# 745 "slexer.ml"

  | 1 ->

  let c = Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 257 "slexer.mll"
      ( (* other character, just copy it over *)
		output_char pfile c;
		preprocess pfile lexbuf
		  
      )
# 756 "slexer.ml"

  | 2 ->
# 262 "slexer.mll"
        (  )
# 761 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state

and rip_ws lexbuf =
    __ocaml_lex_rip_ws_rec lexbuf 73
and __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let ws = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 265 "slexer.mll"
                        ( ws )
# 774 "slexer.ml"

  | 1 ->
# 266 "slexer.mll"
       ( print_string "There must be whitespace after import directive\n"; exit (-1) )
# 779 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state

and get_file_name lexbuf =
    __ocaml_lex_get_file_name_rec lexbuf 75
and __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->

  let fn = Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 269 "slexer.mll"
                                   ( fn )
# 792 "slexer.ml"

  | 1 ->
# 270 "slexer.mll"
      ( print_string "file name following import must be enclosed in double quotes\n"; exit (-1) )
# 797 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state

;;

