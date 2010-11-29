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
	  Error.report_error {Error.error_loc = {start_pos = pos;mid_pos = pos; end_pos = pos;};
						  Error.error_text = msg}

  let keywords = Hashtbl.create 100
  let _ = List.map (fun (k, t) -> Hashtbl.add keywords k t)
	[("assert", ASSERT);
	 ("assume", ASSUME);
	 ("bind", BIND);
	 ("bool", BOOL);
	 ("break", BREAK);
	 ("by", BY);
	 ("case",CASE);
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
   ("time", DTIME);
	 ("to", TO);
	 ("true", TRUE);
	 ("unfold", UNFOLD);
	 ("union", UNION);
	 ("view", VIEW);
	 ("void", VOID);
	 ("where", WHERE);
	 ("while", WHILE);
	 (flow, FLOW flow);]

# 99 "slexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\202\255\001\000\205\255\206\255\078\000\155\000\211\255\
    \212\255\215\255\018\000\031\000\033\000\159\000\226\255\227\255\
    \035\000\168\000\235\255\075\000\170\000\076\000\242\255\184\000\
    \244\255\245\255\246\255\247\255\081\000\250\255\251\255\102\000\
    \181\000\223\255\254\255\255\255\252\255\248\255\195\000\234\255\
    \240\255\231\255\079\000\238\255\236\255\219\255\224\255\233\255\
    \229\255\222\255\225\255\221\255\220\255\216\255\217\255\209\000\
    \203\255\244\000\253\255\254\255\255\255\159\000\250\255\002\000\
    \253\255\254\255\255\255\251\255\001\001\250\255\004\000\253\255\
    \128\000\124\000\255\255\254\255\251\255\012\000\254\255\255\255\
    \005\000\069\000\253\255\254\255\105\000\104\000\106\000\104\000\
    \103\000\255\255\245\000\254\255\246\000\187\000\254\255\003\001\
    \005\001\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\051\000\255\255\255\255\048\000\046\000\255\255\
    \255\255\255\255\037\000\045\000\041\000\042\000\255\255\255\255\
    \027\000\025\000\255\255\018\000\023\000\014\000\255\255\012\000\
    \255\255\255\255\255\255\255\255\006\000\255\255\255\255\002\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\047\000\255\255\
    \255\255\255\255\016\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\003\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\003\000\255\255\
    \005\000\005\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\001\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\000\000\255\255\255\255\001\000\
    \255\255\255\255";
  Lexing.lex_default = 
   "\255\255\000\000\255\255\000\000\000\000\255\255\255\255\000\000\
    \000\000\000\000\255\255\255\255\255\255\255\255\000\000\000\000\
    \255\255\255\255\000\000\255\255\255\255\255\255\000\000\255\255\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \000\000\058\000\000\000\000\000\000\000\062\000\000\000\255\255\
    \000\000\000\000\000\000\000\000\069\000\000\000\255\255\000\000\
    \255\255\255\255\000\000\000\000\000\000\078\000\000\000\000\000\
    \255\255\083\000\000\000\000\000\255\255\255\255\255\255\255\255\
    \255\255\000\000\091\000\000\000\255\255\094\000\000\000\096\000\
    \096\000\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\004\000\003\000\056\000\067\000\002\000\076\000\079\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\079\000\000\000\
    \000\000\080\000\000\000\000\000\000\000\000\000\000\000\000\000\
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
    \005\000\064\000\075\000\074\000\063\000\005\000\084\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\055\000\049\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\046\000\085\000\042\000\
    \086\000\087\000\088\000\089\000\050\000\095\000\000\000\035\000\
    \000\000\000\000\000\000\000\000\034\000\045\000\047\000\041\000\
    \038\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\033\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\038\000\038\000\059\000\092\000\092\000\
    \001\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\071\000\255\255\255\255\070\000\255\255\
    \000\000\000\000\000\000\000\000\059\000\092\000\092\000\000\000\
    \000\000\000\000\065\000\000\000\066\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\000\000\097\000\
    \000\000\000\000\000\000\073\000\000\000\000\000\000\000\000\000\
    \072\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\082\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\060\000\
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
    \255\255\000\000\000\000\002\000\063\000\000\000\070\000\080\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\077\000\255\255\
    \255\255\077\000\255\255\255\255\255\255\255\255\255\255\255\255\
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
    \005\000\061\000\072\000\073\000\061\000\005\000\081\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\006\000\013\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\017\000\084\000\020\000\
    \085\000\086\000\087\000\088\000\013\000\093\000\255\255\032\000\
    \255\255\255\255\255\255\255\255\032\000\017\000\017\000\020\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\032\000\038\000\038\000\038\000\038\000\038\000\
    \038\000\038\000\038\000\038\000\038\000\057\000\090\000\092\000\
    \000\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\068\000\077\000\095\000\068\000\096\000\
    \255\255\255\255\255\255\255\255\057\000\090\000\092\000\255\255\
    \255\255\255\255\061\000\255\255\061\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\095\000\255\255\096\000\
    \255\255\255\255\255\255\068\000\255\255\255\255\255\255\255\255\
    \068\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\081\000\255\255\255\255\
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
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\061\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\093\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\057\000\090\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\068\000\255\255\095\000\255\255\096\000";
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
# 105 "slexer.mll"
         ( 
	  comment_level := 0;
	  comment file_name lexbuf 
	)
# 299 "slexer.ml"

  | 1 ->
# 109 "slexer.mll"
         ( line_comment file_name lexbuf )
# 304 "slexer.ml"

  | 2 ->
# 110 "slexer.mll"
        ( AND )
# 309 "slexer.ml"

  | 3 ->
# 111 "slexer.mll"
         ( ANDAND )
# 314 "slexer.ml"

  | 4 ->
# 112 "slexer.mll"
        ( AT )
# 319 "slexer.ml"

  | 5 ->
# 113 "slexer.mll"
        ( CBRACE )
# 324 "slexer.ml"

  | 6 ->
# 114 "slexer.mll"
        ( COLON )
# 329 "slexer.ml"

  | 7 ->
# 115 "slexer.mll"
         ( COLONCOLON )
# 334 "slexer.ml"

  | 8 ->
# 116 "slexer.mll"
        ( COMMA )
# 339 "slexer.ml"

  | 9 ->
# 117 "slexer.mll"
        ( CPAREN )
# 344 "slexer.ml"

  | 10 ->
# 118 "slexer.mll"
        ( CSQUARE )
# 349 "slexer.ml"

  | 11 ->
# 119 "slexer.mll"
        ( DOLLAR )
# 354 "slexer.ml"

  | 12 ->
# 120 "slexer.mll"
        ( DOT )
# 359 "slexer.ml"

  | 13 ->
# 121 "slexer.mll"
         ( DOUBLEQUOTE )
# 364 "slexer.ml"

  | 14 ->
# 122 "slexer.mll"
        ( EQ )
# 369 "slexer.ml"

  | 15 ->
# 123 "slexer.mll"
         ( EQEQ )
# 374 "slexer.ml"

  | 16 ->
# 124 "slexer.mll"
         ( RIGHTARROW )
# 379 "slexer.ml"

  | 17 ->
# 125 "slexer.mll"
          ( EQUIV )
# 384 "slexer.ml"

  | 18 ->
# 126 "slexer.mll"
        ( GT )
# 389 "slexer.ml"

  | 19 ->
# 127 "slexer.mll"
         ( GTE )
# 394 "slexer.ml"

  | 20 ->
# 128 "slexer.mll"
        ( HASH )
# 399 "slexer.ml"

  | 21 ->
# 129 "slexer.mll"
         ( IMPLY )
# 404 "slexer.ml"

  | 22 ->
# 130 "slexer.mll"
         ( LEFTARROW )
# 409 "slexer.ml"

  | 23 ->
# 131 "slexer.mll"
        ( LT )
# 414 "slexer.ml"

  | 24 ->
# 132 "slexer.mll"
         ( LTE )
# 419 "slexer.ml"

  | 25 ->
# 133 "slexer.mll"
        ( MINUS )
# 424 "slexer.ml"

  | 26 ->
# 134 "slexer.mll"
         ( NEQ )
# 429 "slexer.ml"

  | 27 ->
# 135 "slexer.mll"
        ( NOT )
# 434 "slexer.ml"

  | 28 ->
# 136 "slexer.mll"
        ( OBRACE )
# 439 "slexer.ml"

  | 29 ->
# 137 "slexer.mll"
        ( OPAREN )
# 444 "slexer.ml"

  | 30 ->
# 138 "slexer.mll"
         ( OP_ADD_ASSIGN )
# 449 "slexer.ml"

  | 31 ->
# 139 "slexer.mll"
         ( OP_DEC )
# 454 "slexer.ml"

  | 32 ->
# 140 "slexer.mll"
         ( OP_DIV_ASSIGN )
# 459 "slexer.ml"

  | 33 ->
# 141 "slexer.mll"
         ( OP_INC )
# 464 "slexer.ml"

  | 34 ->
# 142 "slexer.mll"
         ( OP_MOD_ASSIGN )
# 469 "slexer.ml"

  | 35 ->
# 143 "slexer.mll"
         ( OP_MULT_ASSIGN )
# 474 "slexer.ml"

  | 36 ->
# 144 "slexer.mll"
         ( OP_SUB_ASSIGN )
# 479 "slexer.ml"

  | 37 ->
# 145 "slexer.mll"
        ( OR )
# 484 "slexer.ml"

  | 38 ->
# 146 "slexer.mll"
         ( OROR )
# 489 "slexer.ml"

  | 39 ->
# 147 "slexer.mll"
         ( DERIVE )
# 494 "slexer.ml"

  | 40 ->
# 148 "slexer.mll"
        ( OSQUARE )
# 499 "slexer.ml"

  | 41 ->
# 149 "slexer.mll"
        ( PERCENT )
# 504 "slexer.ml"

  | 42 ->
# 150 "slexer.mll"
        ( PLUS )
# 509 "slexer.ml"

  | 43 ->
# 151 "slexer.mll"
         ( PRIME )
# 514 "slexer.ml"

  | 44 ->
# 152 "slexer.mll"
        ( SEMICOLON )
# 519 "slexer.ml"

  | 45 ->
# 153 "slexer.mll"
        ( STAR )
# 524 "slexer.ml"

  | 46 ->
let
# 154 "slexer.mll"
              numstr
# 530 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 154 "slexer.mll"
                     ( LITERAL_INTEGER (int_of_string numstr) )
# 534 "slexer.ml"

  | 47 ->
let
# 155 "slexer.mll"
            numstr
# 540 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 155 "slexer.mll"
                   ( LITERAL_FLOAT (float_of_string numstr) )
# 544 "slexer.ml"

  | 48 ->
let
# 156 "slexer.mll"
                             idstr
# 550 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 157 "slexer.mll"
   (
		if idstr = "_" then
		  IDENTIFIER ("Anon" ^ fresh_trailer ())
		else if idstr = "java" then begin
		  pre_java file_name lexbuf (* search for the first opening brace *)
		end else
		  try Hashtbl.find keywords idstr
		  with | _ -> IDENTIFIER idstr
	  )
# 562 "slexer.ml"

  | 49 ->
# 166 "slexer.mll"
               ( tokenizer file_name lexbuf )
# 567 "slexer.ml"

  | 50 ->
# 167 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 572 "slexer.ml"

  | 51 ->
# 168 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 577 "slexer.ml"

  | 52 ->
# 169 "slexer.mll"
           ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 582 "slexer.ml"

  | 53 ->
# 170 "slexer.mll"
        ( EOF )
# 587 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_tokenizer_rec file_name lexbuf __ocaml_lex_state

and pre_java file_name lexbuf =
    __ocaml_lex_pre_java_rec file_name lexbuf 57
and __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 174 "slexer.mll"
        (
	  java_bcount := 0;
	  Buffer.clear java_code;
	  java file_name lexbuf
	)
# 602 "slexer.ml"

  | 1 ->
# 179 "slexer.mll"
               ( pre_java file_name lexbuf )
# 607 "slexer.ml"

  | 2 ->
# 180 "slexer.mll"
      ( print_error lexbuf "java keyword must be followed by Java code enclosed in {}" )
# 612 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state

and java file_name lexbuf =
    __ocaml_lex_java_rec file_name lexbuf 61
and __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 183 "slexer.mll"
        (
	  if !java_bcount = 0 then
		JAVA (Buffer.contents java_code)
	  else begin
		java_bcount := !java_bcount - 1;
		Buffer.add_char java_code '}';
		java file_name lexbuf
	  end
	)
# 631 "slexer.ml"

  | 1 ->
# 192 "slexer.mll"
        (
	  java_bcount := !java_bcount + 1;
	  Buffer.add_char java_code '{';
	  java file_name lexbuf
	)
# 640 "slexer.ml"

  | 2 ->
# 197 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\n'; 
	  java file_name lexbuf 
	)
# 649 "slexer.ml"

  | 3 ->
# 202 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\r'; 
	  java file_name lexbuf 
	)
# 658 "slexer.ml"

  | 4 ->
# 207 "slexer.mll"
           (
	  incr_linenum file_name lexbuf; 
	  Buffer.add_string java_code "\r\n";
	  java file_name lexbuf 
	)
# 667 "slexer.ml"

  | 5 ->
let
# 212 "slexer.mll"
         c
# 673 "slexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 212 "slexer.mll"
            ( 
	  Buffer.add_char java_code c;
	  java file_name lexbuf 
	)
# 680 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state

and comment file_name lexbuf =
    __ocaml_lex_comment_rec file_name lexbuf 68
and __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 219 "slexer.mll"
         ( 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end
	)
# 698 "slexer.ml"

  | 1 ->
# 227 "slexer.mll"
         (
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf
	)
# 706 "slexer.ml"

  | 2 ->
# 231 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 711 "slexer.ml"

  | 3 ->
# 232 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 716 "slexer.ml"

  | 4 ->
# 233 "slexer.mll"
           ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 721 "slexer.ml"

  | 5 ->
# 234 "slexer.mll"
       ( comment file_name lexbuf )
# 726 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state

and line_comment file_name lexbuf =
    __ocaml_lex_line_comment_rec file_name lexbuf 77
and __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 237 "slexer.mll"
                         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 737 "slexer.ml"

  | 1 ->
# 238 "slexer.mll"
      ( line_comment file_name lexbuf )
# 742 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state

and preprocess pfile lexbuf =
    __ocaml_lex_preprocess_rec pfile lexbuf 81
and __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 242 "slexer.mll"
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
# 770 "slexer.ml"

  | 1 ->
let
# 260 "slexer.mll"
         c
# 776 "slexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 261 "slexer.mll"
      ( (* other character, just copy it over *)
		output_char pfile c;
		preprocess pfile lexbuf
		  
      )
# 784 "slexer.ml"

  | 2 ->
# 266 "slexer.mll"
        (  )
# 789 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state

and rip_ws lexbuf =
    __ocaml_lex_rip_ws_rec lexbuf 90
and __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 269 "slexer.mll"
                     ws
# 801 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 269 "slexer.mll"
                        ( ws )
# 805 "slexer.ml"

  | 1 ->
# 270 "slexer.mll"
       ( print_string "There must be whitespace after import directive\n"; exit (-1) )
# 810 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state

and get_file_name lexbuf =
    __ocaml_lex_get_file_name_rec lexbuf 93
and __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 273 "slexer.mll"
                                fn
# 822 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 273 "slexer.mll"
                                   ( fn )
# 826 "slexer.ml"

  | 1 ->
# 274 "slexer.mll"
      ( print_string "file name following import must be enclosed in double quotes\n"; exit (-1) )
# 831 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state

;;

