type token =
  | INT_LIT of (int)
  | ID of (string)
  | TRUE
  | FALSE
  | FORALL
  | EXISTS
  | OPAREN
  | CPAREN
  | COMMA
  | ENDF
  | OR
  | AND
  | NOT
  | IMPLY
  | GT
  | GTE
  | LT
  | LTE
  | EQ
  | NEQ
  | PLUS
  | MINUS
  | STAR

open Parsing;;
# 2 "rlparser.mly"
  open Globals
  module CP = Cpure
# 31 "rlparser.ml"
let yytransl_const = [|
  259 (* TRUE *);
  260 (* FALSE *);
  261 (* FORALL *);
  262 (* EXISTS *);
  263 (* OPAREN *);
  264 (* CPAREN *);
  265 (* COMMA *);
  266 (* ENDF *);
  267 (* OR *);
  268 (* AND *);
  269 (* NOT *);
  270 (* IMPLY *);
  271 (* GT *);
  272 (* GTE *);
  273 (* LT *);
  274 (* LTE *);
  275 (* EQ *);
  276 (* NEQ *);
  277 (* PLUS *);
  278 (* MINUS *);
  279 (* STAR *);
    0|]

let yytransl_block = [|
  257 (* INT_LIT *);
  258 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\003\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\005\000\005\000\005\000\005\000\005\000\000\000"

let yylen = "\002\000\
\002\000\001\000\003\000\003\000\002\000\006\000\006\000\003\000\
\001\000\001\000\001\000\001\000\003\000\003\000\003\000\003\000\
\003\000\003\000\001\000\001\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\019\000\000\000\010\000\011\000\000\000\000\000\
\000\000\000\000\024\000\000\000\002\000\009\000\000\000\000\000\
\000\000\000\000\005\000\001\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\008\000\000\000\004\000\020\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\023\000\000\000\000\000\
\000\000\000\000\006\000\007\000"

let yydgoto = "\002\000\
\011\000\012\000\013\000\014\000\015\000"

let yysindex = "\002\000\
\054\255\000\000\000\000\000\000\000\000\000\000\001\255\017\255\
\054\255\054\255\000\000\113\255\000\000\000\000\053\255\039\255\
\043\255\103\255\000\000\000\000\054\255\054\255\027\255\027\255\
\027\255\027\255\027\255\027\255\027\255\027\255\027\255\037\255\
\111\255\000\000\050\255\000\000\000\000\106\255\106\255\106\255\
\106\255\106\255\106\255\041\255\041\255\000\000\054\255\054\255\
\105\255\110\255\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\255\254\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\055\255\000\000\000\000\250\254\078\255\083\255\
\088\255\093\255\098\255\015\255\032\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\247\255\000\000\000\000\054\000"

let yytablesize = 129
let yytable = "\018\000\
\019\000\013\000\001\000\013\000\013\000\013\000\012\000\016\000\
\012\000\012\000\012\000\035\000\036\000\020\000\020\000\020\000\
\020\000\020\000\020\000\020\000\020\000\020\000\021\000\017\000\
\021\000\021\000\021\000\003\000\037\000\021\000\021\000\021\000\
\021\000\021\000\021\000\021\000\021\000\049\000\050\000\022\000\
\032\000\022\000\022\000\022\000\033\000\047\000\022\000\022\000\
\022\000\022\000\022\000\022\000\022\000\022\000\003\000\004\000\
\005\000\006\000\007\000\008\000\009\000\022\000\003\000\031\000\
\003\000\003\000\010\000\023\000\024\000\025\000\026\000\027\000\
\028\000\029\000\030\000\031\000\038\000\039\000\040\000\041\000\
\042\000\043\000\044\000\045\000\046\000\014\000\000\000\014\000\
\014\000\014\000\015\000\000\000\015\000\015\000\015\000\016\000\
\000\000\016\000\016\000\016\000\017\000\000\000\017\000\017\000\
\017\000\018\000\000\000\018\000\018\000\018\000\034\000\000\000\
\051\000\021\000\022\000\021\000\022\000\052\000\000\000\048\000\
\021\000\022\000\020\000\021\000\022\000\000\000\029\000\030\000\
\031\000"

let yycheck = "\009\000\
\010\000\008\001\001\000\010\001\011\001\012\001\008\001\007\001\
\010\001\011\001\012\001\021\000\022\000\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\022\001\023\001\008\001\007\001\
\010\001\011\001\012\001\001\001\002\001\015\001\016\001\017\001\
\018\001\019\001\020\001\021\001\022\001\047\000\048\000\008\001\
\002\001\010\001\011\001\012\001\002\001\009\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\001\001\002\001\
\003\001\004\001\005\001\006\001\007\001\012\001\008\001\023\001\
\010\001\011\001\013\001\015\001\016\001\017\001\018\001\019\001\
\020\001\021\001\022\001\023\001\023\000\024\000\025\000\026\000\
\027\000\028\000\029\000\030\000\031\000\008\001\255\255\010\001\
\011\001\012\001\008\001\255\255\010\001\011\001\012\001\008\001\
\255\255\010\001\011\001\012\001\008\001\255\255\010\001\011\001\
\012\001\008\001\255\255\010\001\011\001\012\001\008\001\255\255\
\008\001\011\001\012\001\011\001\012\001\008\001\255\255\009\001\
\011\001\012\001\010\001\011\001\012\001\255\255\021\001\022\001\
\023\001"

let yynames_const = "\
  TRUE\000\
  FALSE\000\
  FORALL\000\
  EXISTS\000\
  OPAREN\000\
  CPAREN\000\
  COMMA\000\
  ENDF\000\
  OR\000\
  AND\000\
  NOT\000\
  IMPLY\000\
  GT\000\
  GTE\000\
  LT\000\
  LTE\000\
  EQ\000\
  NEQ\000\
  PLUS\000\
  MINUS\000\
  STAR\000\
  "

let yynames_block = "\
  INT_LIT\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 31 "rlparser.mly"
                 ( _1 )
# 179 "rlparser.ml"
               : Cpure.formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bformula) in
    Obj.repr(
# 35 "rlparser.mly"
             ( CP.BForm (_1, None) )
# 186 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 36 "rlparser.mly"
                       ( CP.mkOr _1 _3 None no_pos )
# 194 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'formula) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 37 "rlparser.mly"
                        ( CP.mkAnd _1 _3 no_pos )
# 202 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'formula) in
    Obj.repr(
# 38 "rlparser.mly"
                ( CP.mkNot _2 None no_pos )
# 209 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 39 "rlparser.mly"
                                          ( 
      let sv = CP.SpecVar (Int, _3, Unprimed) in
      CP.Forall (sv, _5, None, no_pos) 
    )
# 220 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 43 "rlparser.mly"
                                          (
      let sv = CP.SpecVar (Int, _3, Unprimed) in
      CP.Exists (sv, _5, None, no_pos) 
    )
# 231 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'formula) in
    Obj.repr(
# 47 "rlparser.mly"
                          ( _2 )
# 238 "rlparser.ml"
               : 'formula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'pformula) in
    Obj.repr(
# 50 "rlparser.mly"
                   ( (_1, None) )
# 245 "rlparser.ml"
               : 'bformula))
; (fun __caml_parser_env ->
    Obj.repr(
# 53 "rlparser.mly"
         ( CP.BConst (true, no_pos) )
# 251 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "rlparser.mly"
          ( CP.BConst (false, no_pos) )
# 257 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 55 "rlparser.mly"
       ( CP.mkBVar _1 Unprimed no_pos )
# 264 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 56 "rlparser.mly"
               ( CP.mkGt _1 _3 no_pos )
# 272 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 57 "rlparser.mly"
                ( CP.mkGte _1 _3 no_pos )
# 280 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 58 "rlparser.mly"
               ( CP.mkLt _1 _3 no_pos )
# 288 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 59 "rlparser.mly"
                ( CP.mkLte _1 _3 no_pos )
# 296 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 60 "rlparser.mly"
               ( CP.mkEq _1 _3 no_pos )
# 304 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 61 "rlparser.mly"
                ( CP.mkNeq _1 _3 no_pos )
# 312 "rlparser.ml"
               : 'pformula))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 65 "rlparser.mly"
            ( CP.IConst (_1, no_pos) )
# 319 "rlparser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 66 "rlparser.mly"
       ( CP.mkVar (CP.SpecVar (Int, _1, Unprimed)) no_pos )
# 326 "rlparser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 67 "rlparser.mly"
                 ( CP.mkAdd _1 _3 no_pos)
# 334 "rlparser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 68 "rlparser.mly"
                  ( CP.mkSubtract _1 _3 no_pos )
# 342 "rlparser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 69 "rlparser.mly"
                 ( CP.mkMult _1 _3 no_pos )
# 350 "rlparser.ml"
               : 'exp))
(* Entry input *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let input (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Cpure.formula)
;;
