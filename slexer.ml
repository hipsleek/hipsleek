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
     ("relation",REL); (* An Hoa *)
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

# 100 "slexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\201\255\001\000\204\255\205\255\078\000\155\000\210\255\
    \211\255\214\255\018\000\031\000\033\000\159\000\225\255\226\255\
    \035\000\168\000\234\255\075\000\170\000\076\000\241\255\184\000\
    \243\255\244\255\245\255\246\255\081\000\249\255\067\000\103\000\
    \181\000\222\255\254\255\255\255\252\255\250\255\247\255\195\000\
    \233\255\239\255\230\255\107\000\237\255\235\255\218\255\223\255\
    \232\255\228\255\221\255\224\255\220\255\219\255\215\255\216\255\
    \209\000\202\255\244\000\253\255\254\255\255\255\161\000\250\255\
    \002\000\253\255\254\255\255\255\251\255\001\001\250\255\004\000\
    \253\255\128\000\125\000\255\255\254\255\251\255\012\000\254\255\
    \255\255\005\000\109\000\253\255\254\255\107\000\105\000\107\000\
    \105\000\105\000\255\255\245\000\254\255\246\000\188\000\254\255\
    \003\001\005\001\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\052\000\255\255\255\255\049\000\047\000\255\255\
    \255\255\255\255\038\000\046\000\042\000\043\000\255\255\255\255\
    \028\000\026\000\255\255\019\000\024\000\015\000\255\255\013\000\
    \255\255\255\255\255\255\255\255\007\000\255\255\004\000\002\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\048\000\
    \255\255\255\255\255\255\017\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \003\000\255\255\255\255\255\255\255\255\255\255\255\255\003\000\
    \255\255\005\000\005\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\255\255\255\255\255\255\001\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\000\000\255\255\255\255\
    \001\000\255\255\255\255";
  Lexing.lex_default = 
   "\255\255\000\000\255\255\000\000\000\000\255\255\255\255\000\000\
    \000\000\000\000\255\255\255\255\255\255\255\255\000\000\000\000\
    \255\255\255\255\000\000\255\255\255\255\255\255\000\000\255\255\
    \000\000\000\000\000\000\000\000\255\255\000\000\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \000\000\000\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\059\000\000\000\000\000\000\000\063\000\000\000\
    \255\255\000\000\000\000\000\000\000\000\070\000\000\000\255\255\
    \000\000\255\255\255\255\000\000\000\000\000\000\079\000\000\000\
    \000\000\255\255\084\000\000\000\000\000\255\255\255\255\255\255\
    \255\255\255\255\000\000\092\000\000\000\255\255\095\000\000\000\
    \097\000\097\000\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\004\000\003\000\057\000\068\000\002\000\077\000\080\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\080\000\000\000\
    \000\000\081\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \004\000\016\000\022\000\018\000\024\000\012\000\031\000\008\000\
    \014\000\026\000\011\000\013\000\027\000\017\000\023\000\032\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\028\000\007\000\020\000\021\000\019\000\054\000\
    \030\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\009\000\053\000\025\000\052\000\005\000\
    \049\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\015\000\010\000\029\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \045\000\041\000\040\000\038\000\037\000\036\000\055\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\044\000\076\000\065\000\075\000\005\000\064\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\056\000\050\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\047\000\085\000\043\000\
    \086\000\087\000\088\000\089\000\051\000\090\000\096\000\035\000\
    \000\000\000\000\000\000\000\000\034\000\046\000\048\000\042\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\033\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\060\000\093\000\093\000\
    \001\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\072\000\255\255\255\255\071\000\255\255\
    \000\000\000\000\000\000\000\000\060\000\093\000\093\000\000\000\
    \000\000\000\000\000\000\000\000\066\000\000\000\067\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\000\000\098\000\
    \000\000\000\000\000\000\074\000\000\000\000\000\000\000\000\000\
    \073\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\083\000\000\000\061\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
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
    \255\255\000\000\000\000\002\000\064\000\000\000\071\000\081\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\078\000\255\255\
    \255\255\078\000\255\255\255\255\255\255\255\255\255\255\255\255\
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
    \019\000\021\000\021\000\028\000\030\000\031\000\010\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\043\000\073\000\062\000\074\000\005\000\062\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\006\000\013\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\017\000\082\000\020\000\
    \085\000\086\000\087\000\088\000\013\000\089\000\094\000\032\000\
    \255\255\255\255\255\255\255\255\032\000\017\000\017\000\020\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\032\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\058\000\091\000\093\000\
    \000\000\056\000\056\000\056\000\056\000\056\000\056\000\056\000\
    \056\000\056\000\056\000\069\000\078\000\096\000\069\000\097\000\
    \255\255\255\255\255\255\255\255\058\000\091\000\093\000\255\255\
    \255\255\255\255\255\255\255\255\062\000\255\255\062\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\096\000\255\255\097\000\
    \255\255\255\255\255\255\069\000\255\255\255\255\255\255\255\255\
    \069\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\082\000\255\255\058\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\062\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\094\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\058\000\091\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\069\000\255\255\096\000\255\255\097\000";
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
# 106 "slexer.mll"
         ( 
	  comment_level := 0;
	  comment file_name lexbuf 
	)
# 300 "slexer.ml"

  | 1 ->
# 110 "slexer.mll"
         ( line_comment file_name lexbuf )
# 305 "slexer.ml"

  | 2 ->
# 111 "slexer.mll"
        ( AND )
# 310 "slexer.ml"

  | 3 ->
# 112 "slexer.mll"
         ( ANDAND )
# 315 "slexer.ml"

  | 4 ->
# 113 "slexer.mll"
        ( AT )
# 320 "slexer.ml"

  | 5 ->
# 114 "slexer.mll"
         (IMM)
# 325 "slexer.ml"

  | 6 ->
# 115 "slexer.mll"
        ( CBRACE )
# 330 "slexer.ml"

  | 7 ->
# 116 "slexer.mll"
        ( COLON )
# 335 "slexer.ml"

  | 8 ->
# 117 "slexer.mll"
         ( COLONCOLON )
# 340 "slexer.ml"

  | 9 ->
# 118 "slexer.mll"
        ( COMMA )
# 345 "slexer.ml"

  | 10 ->
# 119 "slexer.mll"
        ( CPAREN )
# 350 "slexer.ml"

  | 11 ->
# 120 "slexer.mll"
        ( CSQUARE )
# 355 "slexer.ml"

  | 12 ->
# 121 "slexer.mll"
        ( DOLLAR )
# 360 "slexer.ml"

  | 13 ->
# 122 "slexer.mll"
        ( DOT )
# 365 "slexer.ml"

  | 14 ->
# 123 "slexer.mll"
         ( DOUBLEQUOTE )
# 370 "slexer.ml"

  | 15 ->
# 124 "slexer.mll"
        ( EQ )
# 375 "slexer.ml"

  | 16 ->
# 125 "slexer.mll"
         ( EQEQ )
# 380 "slexer.ml"

  | 17 ->
# 126 "slexer.mll"
         ( RIGHTARROW )
# 385 "slexer.ml"

  | 18 ->
# 127 "slexer.mll"
          ( EQUIV )
# 390 "slexer.ml"

  | 19 ->
# 128 "slexer.mll"
        ( GT )
# 395 "slexer.ml"

  | 20 ->
# 129 "slexer.mll"
         ( GTE )
# 400 "slexer.ml"

  | 21 ->
# 130 "slexer.mll"
        ( HASH )
# 405 "slexer.ml"

  | 22 ->
# 131 "slexer.mll"
         ( IMPLY )
# 410 "slexer.ml"

  | 23 ->
# 132 "slexer.mll"
         ( LEFTARROW )
# 415 "slexer.ml"

  | 24 ->
# 133 "slexer.mll"
        ( LT )
# 420 "slexer.ml"

  | 25 ->
# 134 "slexer.mll"
         ( LTE )
# 425 "slexer.ml"

  | 26 ->
# 135 "slexer.mll"
        ( MINUS )
# 430 "slexer.ml"

  | 27 ->
# 136 "slexer.mll"
         ( NEQ )
# 435 "slexer.ml"

  | 28 ->
# 137 "slexer.mll"
        ( NOT )
# 440 "slexer.ml"

  | 29 ->
# 138 "slexer.mll"
        ( OBRACE )
# 445 "slexer.ml"

  | 30 ->
# 139 "slexer.mll"
        ( OPAREN )
# 450 "slexer.ml"

  | 31 ->
# 140 "slexer.mll"
         ( OP_ADD_ASSIGN )
# 455 "slexer.ml"

  | 32 ->
# 141 "slexer.mll"
         ( OP_DEC )
# 460 "slexer.ml"

  | 33 ->
# 142 "slexer.mll"
         ( OP_DIV_ASSIGN )
# 465 "slexer.ml"

  | 34 ->
# 143 "slexer.mll"
         ( OP_INC )
# 470 "slexer.ml"

  | 35 ->
# 144 "slexer.mll"
         ( OP_MOD_ASSIGN )
# 475 "slexer.ml"

  | 36 ->
# 145 "slexer.mll"
         ( OP_MULT_ASSIGN )
# 480 "slexer.ml"

  | 37 ->
# 146 "slexer.mll"
         ( OP_SUB_ASSIGN )
# 485 "slexer.ml"

  | 38 ->
# 147 "slexer.mll"
        ( OR )
# 490 "slexer.ml"

  | 39 ->
# 148 "slexer.mll"
         ( OROR )
# 495 "slexer.ml"

  | 40 ->
# 149 "slexer.mll"
         ( DERIVE )
# 500 "slexer.ml"

  | 41 ->
# 150 "slexer.mll"
        ( OSQUARE )
# 505 "slexer.ml"

  | 42 ->
# 151 "slexer.mll"
        ( PERCENT )
# 510 "slexer.ml"

  | 43 ->
# 152 "slexer.mll"
        ( PLUS )
# 515 "slexer.ml"

  | 44 ->
# 153 "slexer.mll"
         ( PRIME )
# 520 "slexer.ml"

  | 45 ->
# 154 "slexer.mll"
        ( SEMICOLON )
# 525 "slexer.ml"

  | 46 ->
# 155 "slexer.mll"
        ( STAR )
# 530 "slexer.ml"

  | 47 ->
let
# 156 "slexer.mll"
              numstr
# 536 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 156 "slexer.mll"
                     ( LITERAL_INTEGER (int_of_string numstr) )
# 540 "slexer.ml"

  | 48 ->
let
# 157 "slexer.mll"
            numstr
# 546 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 157 "slexer.mll"
                   ( LITERAL_FLOAT (float_of_string numstr) )
# 550 "slexer.ml"

  | 49 ->
let
# 158 "slexer.mll"
                             idstr
# 556 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 159 "slexer.mll"
   (
		if idstr = "_" then
		  IDENTIFIER ("Anon" ^ fresh_trailer ())
		else if idstr = "java" then begin
		  pre_java file_name lexbuf (* search for the first opening brace *)
		end else
		  try Hashtbl.find keywords idstr
		  with | _ -> IDENTIFIER idstr
	  )
# 568 "slexer.ml"

  | 50 ->
# 168 "slexer.mll"
               ( tokenizer file_name lexbuf )
# 573 "slexer.ml"

  | 51 ->
# 169 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 578 "slexer.ml"

  | 52 ->
# 170 "slexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 583 "slexer.ml"

  | 53 ->
# 171 "slexer.mll"
           ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 588 "slexer.ml"

  | 54 ->
# 172 "slexer.mll"
        ( EOF )
# 593 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_tokenizer_rec file_name lexbuf __ocaml_lex_state

and pre_java file_name lexbuf =
  __ocaml_lex_pre_java_rec file_name lexbuf 58
and __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 176 "slexer.mll"
        (
	  java_bcount := 0;
	  Buffer.clear java_code;
	  java file_name lexbuf
	)
# 608 "slexer.ml"

  | 1 ->
# 181 "slexer.mll"
               ( pre_java file_name lexbuf )
# 613 "slexer.ml"

  | 2 ->
# 182 "slexer.mll"
      ( print_error lexbuf "java keyword must be followed by Java code enclosed in {}" )
# 618 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state

and java file_name lexbuf =
  __ocaml_lex_java_rec file_name lexbuf 62
and __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 185 "slexer.mll"
        (
	  if !java_bcount = 0 then
		JAVA (Buffer.contents java_code)
	  else begin
		java_bcount := !java_bcount - 1;
		Buffer.add_char java_code '}';
		java file_name lexbuf
	  end
	)
# 637 "slexer.ml"

  | 1 ->
# 194 "slexer.mll"
        (
	  java_bcount := !java_bcount + 1;
	  Buffer.add_char java_code '{';
	  java file_name lexbuf
	)
# 646 "slexer.ml"

  | 2 ->
# 199 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\n'; 
	  java file_name lexbuf 
	)
# 655 "slexer.ml"

  | 3 ->
# 204 "slexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\r'; 
	  java file_name lexbuf 
	)
# 664 "slexer.ml"

  | 4 ->
# 209 "slexer.mll"
           (
	  incr_linenum file_name lexbuf; 
	  Buffer.add_string java_code "\r\n";
	  java file_name lexbuf 
	)
# 673 "slexer.ml"

  | 5 ->
let
# 214 "slexer.mll"
         c
# 679 "slexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 214 "slexer.mll"
            ( 
	  Buffer.add_char java_code c;
	  java file_name lexbuf 
	)
# 686 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state

and comment file_name lexbuf =
  __ocaml_lex_comment_rec file_name lexbuf 69
and __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 221 "slexer.mll"
         ( 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end
	)
# 704 "slexer.ml"

  | 1 ->
# 229 "slexer.mll"
         (
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf
	)
# 712 "slexer.ml"

  | 2 ->
# 233 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 717 "slexer.ml"

  | 3 ->
# 234 "slexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 722 "slexer.ml"

  | 4 ->
# 235 "slexer.mll"
           ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 727 "slexer.ml"

  | 5 ->
# 236 "slexer.mll"
       ( comment file_name lexbuf )
# 732 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state

and line_comment file_name lexbuf =
  __ocaml_lex_line_comment_rec file_name lexbuf 78
and __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 239 "slexer.mll"
                         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 743 "slexer.ml"

  | 1 ->
# 240 "slexer.mll"
      ( line_comment file_name lexbuf )
# 748 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state

and preprocess pfile lexbuf =
  __ocaml_lex_preprocess_rec pfile lexbuf 82
and __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 244 "slexer.mll"
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
# 776 "slexer.ml"

  | 1 ->
let
# 262 "slexer.mll"
         c
# 782 "slexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 263 "slexer.mll"
      ( (* other character, just copy it over *)
		output_char pfile c;
		preprocess pfile lexbuf
		  
      )
# 790 "slexer.ml"

  | 2 ->
# 268 "slexer.mll"
        (  )
# 795 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state

and rip_ws lexbuf =
  __ocaml_lex_rip_ws_rec lexbuf 91
and __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 271 "slexer.mll"
                     ws
# 807 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 271 "slexer.mll"
                        ( ws )
# 811 "slexer.ml"

  | 1 ->
# 272 "slexer.mll"
       ( print_string "There must be whitespace after import directive\n"; exit (-1) )
# 816 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state

and get_file_name lexbuf =
  __ocaml_lex_get_file_name_rec lexbuf 94
and __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 275 "slexer.mll"
                                fn
# 828 "slexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 275 "slexer.mll"
                                   ( fn )
# 832 "slexer.ml"

  | 1 ->
# 276 "slexer.mll"
      ( print_string "file name following import must be enclosed in double quotes\n"; exit (-1) )
# 837 "slexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state

;;

