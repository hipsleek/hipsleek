# 1 "ilexer.mll"
 
  open Globals
  open Iparser

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
	[("alln", ALLN);
	 ("app", APPEND);
	 ("assert", ASSERT);
	 ("assume", ASSUME);
	 ("bind", BIND);
	 ("bool", BOOL);
	 ("break", BREAK);
	 ("case",CASE);
	 ("class", CLASS);
	 ("coercion", COERCION);
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
	 ("head", HEAD);
	 ("if", IF);
	 ("@I", IMM);
	 ("implies", IMPLIES);
	 ("import", IMPORT);
	 ("in", IN);
	 ("inlist", INLIST);
	 ("int", INT);
	 ("intersect", INTERSECT);
	 ("inv", INV);
	 ("len", LENGTH);
	 ("max", MAX);
	 ("min", MIN);
	 ("bagmax", BAGMAX);
	 ("bagmin", BAGMIN);
	 ("new", NEW);
	 ("notin", NOTIN);
	 ("notinlist", NOTINLIST);
	 ("null", NULL);
	 ("off", OFF);
	 ("on", ON);
	 ("or", ORWORD);
     ("perm", PERM);
	 ("dprint", PRINT);
	 ("ref", REF);
     ("relation",REL); (* An Hoa *)
	 ("requires", REQUIRES);
	 ("res", RES "res");
	 ("rev", REVERSE);
	 ("return", RETURN);
	 ("self", SELF "self");
	 ("split", SPLIT);
	 ("subset", SUBSET);
	 ("static", STATIC);
	 ("tail", TAIL);
	 ("then", THEN);
	 ("this", THIS "this");
     ("time", DTIME);
	 ("to", TO);
	 ("true", TRUE);
	 ("unfold", UNFOLD);
	 ("union", UNION);
	 ("variance", VARIANCE);
	 ("view", VIEW);
	 ("void", VOID);
	 ("where", WHERE);
	 ("while", WHILE);
     ("global", GLOBAL);
	 (*exception related*)
	 (flow, FLOW flow);
	 ("try", TRY);
	 ("catch", CATCH);
	 ("finally", FINALLY);
	 ("throws", THROWS);
	 ("raise",RAISE);
	]

# 112 "ilexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\197\255\001\000\200\255\201\255\078\000\155\000\208\255\
    \209\255\002\000\031\000\159\000\222\255\012\000\224\255\033\000\
    \168\000\232\255\035\000\170\000\076\000\239\255\184\000\241\255\
    \242\255\243\255\046\000\245\255\082\000\249\255\068\000\104\000\
    \181\000\219\255\254\255\255\255\252\255\250\255\111\000\246\255\
    \213\255\244\255\195\000\231\255\109\000\205\255\228\255\110\000\
    \235\255\233\255\215\255\220\255\230\255\226\255\223\255\218\255\
    \221\255\217\255\216\255\209\000\198\255\244\000\253\255\254\255\
    \255\255\204\000\250\255\002\000\253\255\254\255\255\255\251\255\
    \001\001\250\255\004\000\253\255\132\000\169\000\255\255\254\255\
    \251\255\012\000\254\255\255\255\005\000\113\000\253\255\254\255\
    \110\000\109\000\111\000\110\000\109\000\255\255\245\000\254\255\
    \246\000\192\000\254\255\003\001\005\001\255\255";
  Lexing.lex_backtrk = 
   "\255\255\255\255\056\000\255\255\255\255\053\000\051\000\255\255\
    \255\255\048\000\044\000\045\000\255\255\043\000\255\255\030\000\
    \028\000\255\255\021\000\026\000\017\000\255\255\015\000\255\255\
    \255\255\255\255\041\000\255\255\007\000\255\255\004\000\002\000\
    \049\000\255\255\255\255\255\255\255\255\255\255\008\000\255\255\
    \255\255\255\255\052\000\255\255\018\000\255\255\255\255\019\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\003\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\003\000\255\255\005\000\005\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\000\000\255\255\255\255\255\255\
    \001\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\001\000\255\255\255\255";
  Lexing.lex_default = 
   "\255\255\000\000\255\255\000\000\000\000\255\255\255\255\000\000\
    \000\000\255\255\255\255\255\255\000\000\255\255\000\000\255\255\
    \255\255\000\000\255\255\255\255\255\255\000\000\255\255\000\000\
    \000\000\000\000\255\255\000\000\255\255\000\000\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\000\000\255\255\000\000\255\255\000\000\000\000\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\000\000\062\000\000\000\000\000\
    \000\000\066\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \073\000\000\000\255\255\000\000\255\255\255\255\000\000\000\000\
    \000\000\082\000\000\000\000\000\255\255\087\000\000\000\000\000\
    \255\255\255\255\255\255\255\255\255\255\000\000\095\000\000\000\
    \255\255\098\000\000\000\100\000\100\000\000\000";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\004\000\003\000\060\000\071\000\002\000\080\000\083\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\083\000\000\000\
    \000\000\084\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \004\000\015\000\021\000\017\000\023\000\010\000\031\000\008\000\
    \012\000\025\000\009\000\011\000\027\000\016\000\022\000\032\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\028\000\007\000\019\000\020\000\018\000\058\000\
    \030\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\013\000\057\000\024\000\053\000\005\000\
    \049\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\014\000\026\000\029\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \054\000\044\000\043\000\041\000\038\000\037\000\036\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\039\000\040\000\045\000\048\000\005\000\079\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\059\000\055\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\051\000\068\000\047\000\
    \078\000\067\000\088\000\089\000\056\000\090\000\091\000\035\000\
    \092\000\093\000\099\000\000\000\034\000\050\000\052\000\046\000\
    \042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\033\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\063\000\096\000\096\000\
    \001\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\075\000\255\255\255\255\074\000\255\255\
    \000\000\000\000\000\000\000\000\063\000\096\000\096\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\255\255\000\000\101\000\
    \000\000\000\000\000\000\077\000\000\000\000\000\000\000\000\000\
    \076\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\069\000\
    \000\000\070\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\064\000\
    \000\000\086\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\255\255\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\255\255\000\000\255\255";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\002\000\067\000\000\000\074\000\084\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\081\000\255\255\
    \255\255\081\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\010\000\000\000\015\000\000\000\
    \018\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \013\000\020\000\020\000\026\000\028\000\030\000\031\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\038\000\026\000\044\000\047\000\005\000\076\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
    \005\000\006\000\011\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\016\000\065\000\019\000\
    \077\000\065\000\085\000\088\000\011\000\089\000\090\000\032\000\
    \091\000\092\000\097\000\255\255\032\000\016\000\016\000\019\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\032\000\042\000\042\000\042\000\042\000\042\000\
    \042\000\042\000\042\000\042\000\042\000\061\000\094\000\096\000\
    \000\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\072\000\081\000\099\000\072\000\100\000\
    \255\255\255\255\255\255\255\255\061\000\094\000\096\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\099\000\255\255\100\000\
    \255\255\255\255\255\255\072\000\255\255\255\255\255\255\255\255\
    \072\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\065\000\
    \255\255\065\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\061\000\
    \255\255\085\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \097\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\065\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\061\000\094\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\072\000\255\255\099\000\255\255\100\000";
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
# 118 "ilexer.mll"
         ( 
	  comment_level := 0;
	  comment file_name lexbuf 
	)
# 312 "ilexer.ml"

  | 1 ->
# 122 "ilexer.mll"
         ( line_comment file_name lexbuf )
# 317 "ilexer.ml"

  | 2 ->
# 123 "ilexer.mll"
        ( AND )
# 322 "ilexer.ml"

  | 3 ->
# 124 "ilexer.mll"
         ( ANDAND )
# 327 "ilexer.ml"

  | 4 ->
# 125 "ilexer.mll"
        ( AT )
# 332 "ilexer.ml"

  | 5 ->
# 126 "ilexer.mll"
         (IMM)
# 337 "ilexer.ml"

  | 6 ->
# 127 "ilexer.mll"
        ( CBRACE )
# 342 "ilexer.ml"

  | 7 ->
# 128 "ilexer.mll"
        ( COLON )
# 347 "ilexer.ml"

  | 8 ->
# 129 "ilexer.mll"
         ( COLONCOLON )
# 352 "ilexer.ml"

  | 9 ->
# 130 "ilexer.mll"
          ( COLONCOLONCOLON )
# 357 "ilexer.ml"

  | 10 ->
# 131 "ilexer.mll"
        ( COMMA )
# 362 "ilexer.ml"

  | 11 ->
# 132 "ilexer.mll"
         ( CLIST )
# 367 "ilexer.ml"

  | 12 ->
# 133 "ilexer.mll"
        ( CPAREN )
# 372 "ilexer.ml"

  | 13 ->
# 134 "ilexer.mll"
        ( CSQUARE )
# 377 "ilexer.ml"

  | 14 ->
# 135 "ilexer.mll"
        ( DOLLAR )
# 382 "ilexer.ml"

  | 15 ->
# 136 "ilexer.mll"
        ( DOT )
# 387 "ilexer.ml"

  | 16 ->
# 137 "ilexer.mll"
         ( DOUBLEQUOTE )
# 392 "ilexer.ml"

  | 17 ->
# 138 "ilexer.mll"
        ( EQ )
# 397 "ilexer.ml"

  | 18 ->
# 139 "ilexer.mll"
         ( EQEQ )
# 402 "ilexer.ml"

  | 19 ->
# 140 "ilexer.mll"
         ( RIGHTARROW )
# 407 "ilexer.ml"

  | 20 ->
# 141 "ilexer.mll"
          ( EQUIV )
# 412 "ilexer.ml"

  | 21 ->
# 142 "ilexer.mll"
        ( GT )
# 417 "ilexer.ml"

  | 22 ->
# 143 "ilexer.mll"
         ( GTE )
# 422 "ilexer.ml"

  | 23 ->
# 144 "ilexer.mll"
        ( HASH )
# 427 "ilexer.ml"

  | 24 ->
# 145 "ilexer.mll"
         ( IMPLY )
# 432 "ilexer.ml"

  | 25 ->
# 146 "ilexer.mll"
         ( LEFTARROW )
# 437 "ilexer.ml"

  | 26 ->
# 147 "ilexer.mll"
        ( LT )
# 442 "ilexer.ml"

  | 27 ->
# 148 "ilexer.mll"
         ( LTE )
# 447 "ilexer.ml"

  | 28 ->
# 149 "ilexer.mll"
        ( MINUS )
# 452 "ilexer.ml"

  | 29 ->
# 150 "ilexer.mll"
         ( NEQ )
# 457 "ilexer.ml"

  | 30 ->
# 151 "ilexer.mll"
        ( NOT )
# 462 "ilexer.ml"

  | 31 ->
# 152 "ilexer.mll"
        ( OBRACE )
# 467 "ilexer.ml"

  | 32 ->
# 153 "ilexer.mll"
         ( OLIST )
# 472 "ilexer.ml"

  | 33 ->
# 154 "ilexer.mll"
        ( OPAREN )
# 477 "ilexer.ml"

  | 34 ->
# 155 "ilexer.mll"
         ( OP_ADD_ASSIGN )
# 482 "ilexer.ml"

  | 35 ->
# 156 "ilexer.mll"
         ( OP_DEC )
# 487 "ilexer.ml"

  | 36 ->
# 157 "ilexer.mll"
         ( OP_DIV_ASSIGN )
# 492 "ilexer.ml"

  | 37 ->
# 158 "ilexer.mll"
         ( OP_INC )
# 497 "ilexer.ml"

  | 38 ->
# 159 "ilexer.mll"
         ( OP_MOD_ASSIGN )
# 502 "ilexer.ml"

  | 39 ->
# 160 "ilexer.mll"
         ( OP_MULT_ASSIGN )
# 507 "ilexer.ml"

  | 40 ->
# 161 "ilexer.mll"
         ( OP_SUB_ASSIGN )
# 512 "ilexer.ml"

  | 41 ->
# 162 "ilexer.mll"
        ( OR )
# 517 "ilexer.ml"

  | 42 ->
# 163 "ilexer.mll"
         ( OROR )
# 522 "ilexer.ml"

  | 43 ->
# 164 "ilexer.mll"
        ( OSQUARE )
# 527 "ilexer.ml"

  | 44 ->
# 165 "ilexer.mll"
        ( PERCENT )
# 532 "ilexer.ml"

  | 45 ->
# 166 "ilexer.mll"
        ( PLUS )
# 537 "ilexer.ml"

  | 46 ->
# 167 "ilexer.mll"
         ( PRIME )
# 542 "ilexer.ml"

  | 47 ->
# 168 "ilexer.mll"
        ( SEMICOLON )
# 547 "ilexer.ml"

  | 48 ->
# 169 "ilexer.mll"
        ( STAR )
# 552 "ilexer.ml"

  | 49 ->
# 170 "ilexer.mll"
        ( DIV )
# 557 "ilexer.ml"

  | 50 ->
# 171 "ilexer.mll"
          ( ESCAPE )
# 562 "ilexer.ml"

  | 51 ->
let
# 172 "ilexer.mll"
              numstr
# 568 "ilexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 172 "ilexer.mll"
                     ( LITERAL_INTEGER (int_of_string numstr) )
# 572 "ilexer.ml"

  | 52 ->
let
# 173 "ilexer.mll"
            numstr
# 578 "ilexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 173 "ilexer.mll"
                   ( LITERAL_FLOAT (float_of_string numstr) )
# 582 "ilexer.ml"

  | 53 ->
let
# 174 "ilexer.mll"
                             idstr
# 588 "ilexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 175 "ilexer.mll"
   (
		if idstr = "_" then
			begin
				IDENTIFIER ("Anon" ^ fresh_trailer ())
		  end
		else if idstr = "java" then begin
		  pre_java file_name lexbuf (* search for the first opening brace *)
		end else
		  try Hashtbl.find keywords idstr
		  with | _ -> IDENTIFIER idstr
	  )
# 602 "ilexer.ml"

  | 54 ->
# 186 "ilexer.mll"
               ( tokenizer file_name lexbuf )
# 607 "ilexer.ml"

  | 55 ->
# 187 "ilexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 612 "ilexer.ml"

  | 56 ->
# 188 "ilexer.mll"
         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 617 "ilexer.ml"

  | 57 ->
# 189 "ilexer.mll"
           ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 622 "ilexer.ml"

  | 58 ->
# 190 "ilexer.mll"
        ( EOF )
# 627 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_tokenizer_rec file_name lexbuf __ocaml_lex_state

and pre_java file_name lexbuf =
  __ocaml_lex_pre_java_rec file_name lexbuf 61
and __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 194 "ilexer.mll"
        (
	  java_bcount := 0;
	  Buffer.clear java_code;
	  java file_name lexbuf
	)
# 642 "ilexer.ml"

  | 1 ->
# 199 "ilexer.mll"
               ( pre_java file_name lexbuf )
# 647 "ilexer.ml"

  | 2 ->
# 200 "ilexer.mll"
      ( print_error lexbuf "java keyword must be followed by Java code enclosed in {}" )
# 652 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_pre_java_rec file_name lexbuf __ocaml_lex_state

and java file_name lexbuf =
  __ocaml_lex_java_rec file_name lexbuf 65
and __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 203 "ilexer.mll"
        (
	  if !java_bcount = 0 then
		JAVA (Buffer.contents java_code)
	  else begin
		java_bcount := !java_bcount - 1;
		Buffer.add_char java_code '}';
		java file_name lexbuf
	  end
	)
# 671 "ilexer.ml"

  | 1 ->
# 212 "ilexer.mll"
        (
	  java_bcount := !java_bcount + 1;
	  Buffer.add_char java_code '{';
	  java file_name lexbuf
	)
# 680 "ilexer.ml"

  | 2 ->
# 217 "ilexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\n'; 
	  java file_name lexbuf 
	)
# 689 "ilexer.ml"

  | 3 ->
# 222 "ilexer.mll"
         ( 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\r'; 
	  java file_name lexbuf 
	)
# 698 "ilexer.ml"

  | 4 ->
# 227 "ilexer.mll"
           (
	  incr_linenum file_name lexbuf; 
	  Buffer.add_string java_code "\r\n";
	  java file_name lexbuf 
	)
# 707 "ilexer.ml"

  | 5 ->
let
# 232 "ilexer.mll"
         c
# 713 "ilexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 232 "ilexer.mll"
            ( 
	  Buffer.add_char java_code c;
	  java file_name lexbuf 
	)
# 720 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_java_rec file_name lexbuf __ocaml_lex_state

and comment file_name lexbuf =
  __ocaml_lex_comment_rec file_name lexbuf 72
and __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 238 "ilexer.mll"
         ( 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end
	)
# 738 "ilexer.ml"

  | 1 ->
# 246 "ilexer.mll"
         (
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf
	)
# 746 "ilexer.ml"

  | 2 ->
# 250 "ilexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 751 "ilexer.ml"

  | 3 ->
# 251 "ilexer.mll"
         ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 756 "ilexer.ml"

  | 4 ->
# 252 "ilexer.mll"
           ( incr_linenum file_name lexbuf; comment file_name lexbuf )
# 761 "ilexer.ml"

  | 5 ->
# 253 "ilexer.mll"
       ( comment file_name lexbuf )
# 766 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec file_name lexbuf __ocaml_lex_state

and line_comment file_name lexbuf =
  __ocaml_lex_line_comment_rec file_name lexbuf 81
and __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 256 "ilexer.mll"
                         ( incr_linenum file_name lexbuf; tokenizer file_name lexbuf )
# 777 "ilexer.ml"

  | 1 ->
# 257 "ilexer.mll"
      ( line_comment file_name lexbuf )
# 782 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_line_comment_rec file_name lexbuf __ocaml_lex_state

and preprocess pfile lexbuf =
  __ocaml_lex_preprocess_rec pfile lexbuf 85
and __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 261 "ilexer.mll"
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
# 810 "ilexer.ml"

  | 1 ->
let
# 279 "ilexer.mll"
         c
# 816 "ilexer.ml"
= Lexing.sub_lexeme_char lexbuf lexbuf.Lexing.lex_start_pos in
# 280 "ilexer.mll"
      ( (* other character, just copy it over *)
		output_char pfile c;
		preprocess pfile lexbuf
		  
      )
# 824 "ilexer.ml"

  | 2 ->
# 285 "ilexer.mll"
        (  )
# 829 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_preprocess_rec pfile lexbuf __ocaml_lex_state

and rip_ws lexbuf =
  __ocaml_lex_rip_ws_rec lexbuf 94
and __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 288 "ilexer.mll"
                     ws
# 841 "ilexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 288 "ilexer.mll"
                        ( ws )
# 845 "ilexer.ml"

  | 1 ->
# 289 "ilexer.mll"
       ( print_string "There must be whitespace after import directive\n"; exit (-1) )
# 850 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_rip_ws_rec lexbuf __ocaml_lex_state

and get_file_name lexbuf =
  __ocaml_lex_get_file_name_rec lexbuf 97
and __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
let
# 292 "ilexer.mll"
                                fn
# 862 "ilexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 292 "ilexer.mll"
                                   ( fn )
# 866 "ilexer.ml"

  | 1 ->
# 293 "ilexer.mll"
      ( print_string "file name following import must be enclosed in double quotes\n"; exit (-1) )
# 871 "ilexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_get_file_name_rec lexbuf __ocaml_lex_state

;;

