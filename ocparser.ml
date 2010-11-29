type token =
  | AND
  | BOOL
  | CBRACE
  | COLON
  | COMMA
  | CPAREN
  | CSQUARE
  | DOT
  | EQ
  | EOF
  | EQEQ
  | EXISTS
  | FALSE
  | FORALL
  | GT
  | GTE
  | ICONST of (int)
  | ID of (string)
  | IDPRIMED of (string)
  | LT
  | LTE
  | MINUS
  | NEQ
  | NOT
  | OBRACE
  | OPAREN
  | OR
  | OSQUARE
  | PLUS
  | PRINT
  | SEMICOLON
  | TIMES
  | TRUE
  | UNION

open Parsing;;
# 2 "ocparser.mly"
  open Globals
  open Cpure

  module Err = Error
  let subst_lst = ref ([]:(string*string*typ)list)
  
  (*let get_pos p = Parsing.rhs_start_pos p*)
  let get_pos x = 
				{start_pos = Parsing.symbol_start_pos ();
				 end_pos = Parsing. symbol_end_pos ();
				 mid_pos = Parsing.rhs_start_pos x;
				}	
  let rec trans_null (b:formula):formula = 
    let rec trans_b_f_null b = match b with
      | Lt (e1,e2,p) -> (match (e1,e2) with
            | IConst (i,_), Var(v,l) ->  if (is_object_var v) then if (i>=0) then Neq(e2,Null l,p) else BConst (true,p) else b
            | Var (v,l), IConst (i,_) -> if (is_object_var v) then if (i<=1) then Eq(e1,Null l,p) else BConst(true,p) else b          
            | _ -> b)
      | Lte(e1,e2,p) ->(match (e1,e2) with
            | IConst (i,_), Var(v,l) ->  if (is_object_var v) then if (i>=1) then Neq(e2,Null l,p) else BConst (true,p) else b
            | Var (v,l), IConst (i,_) -> if (is_object_var v) then if (i<1) then Eq(e1,Null l,p) else BConst(true,p) else b          
            | _ -> b) 
      | Gt (e1,e2,p) -> trans_b_f_null (Lt (e2,e1,p))
      | Gte(e1,e2,p) -> trans_b_f_null (Lte (e2,e1,p))
      | _ -> b in
    match b with
      | BForm (b,l) -> BForm ((trans_b_f_null b),l)
      | And (f1,f2,l) -> mkAnd (trans_null f1) (trans_null f2) l
      | Or (f1,f2,fl,l) -> mkOr (trans_null f1) (trans_null f2) fl l
      | Not (f,fl,l) -> Not ((trans_null f),fl,l)
      | Forall (sv,f,fl,l) -> Forall(sv,(trans_null f),fl,l)
      | Exists (sv,f,fl,l) -> Exists(sv,(trans_null f),fl,l)
# 72 "ocparser.ml"
let yytransl_const = [|
  257 (* AND *);
  258 (* BOOL *);
  259 (* CBRACE *);
  260 (* COLON *);
  261 (* COMMA *);
  262 (* CPAREN *);
  263 (* CSQUARE *);
  264 (* DOT *);
  265 (* EQ *);
    0 (* EOF *);
  266 (* EQEQ *);
  267 (* EXISTS *);
  268 (* FALSE *);
  269 (* FORALL *);
  270 (* GT *);
  271 (* GTE *);
  275 (* LT *);
  276 (* LTE *);
  277 (* MINUS *);
  278 (* NEQ *);
  279 (* NOT *);
  280 (* OBRACE *);
  281 (* OPAREN *);
  282 (* OR *);
  283 (* OSQUARE *);
  284 (* PLUS *);
  285 (* PRINT *);
  286 (* SEMICOLON *);
  287 (* TIMES *);
  288 (* TRUE *);
  289 (* UNION *);
    0|]

let yytransl_block = [|
  272 (* ICONST *);
  273 (* ID *);
  274 (* IDPRIMED *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\004\000\004\000\
\004\000\005\000\005\000\005\000\005\000\005\000\005\000\005\000\
\007\000\007\000\007\000\007\000\007\000\007\000\007\000\007\000\
\008\000\008\000\008\000\008\000\008\000\008\000\003\000\003\000\
\010\000\010\000\006\000\006\000\011\000\011\000\009\000\009\000\
\000\000"

let yylen = "\002\000\
\001\000\003\000\007\000\005\000\003\000\003\000\003\000\001\000\
\006\000\001\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\001\000\001\000\
\001\000\001\000\002\000\003\000\003\000\002\000\000\000\001\000\
\001\000\003\000\000\000\001\000\001\000\003\000\001\000\001\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\041\000\000\000\000\000\000\000\000\000\
\000\000\006\000\000\000\039\000\040\000\000\000\000\000\000\000\
\025\000\000\000\005\000\002\000\027\000\030\000\000\000\000\000\
\000\000\000\000\004\000\000\000\029\000\028\000\000\000\000\000\
\024\000\023\000\000\000\000\000\000\000\010\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\003\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\037\000\000\000\
\021\000\019\000\020\000\017\000\018\000\022\000\007\000\015\000\
\013\000\014\000\011\000\012\000\016\000\000\000\000\000\000\000\
\038\000\009\000"

let yydgoto = "\002\000\
\004\000\005\000\035\000\036\000\037\000\054\000\038\000\016\000\
\017\000\018\000\056\000"

let yysindex = "\012\000\
\250\254\000\000\255\254\000\000\253\254\037\255\062\255\038\255\
\250\254\000\000\007\255\000\000\000\000\062\255\042\255\240\254\
\000\000\046\255\000\000\000\000\000\000\000\000\029\255\062\255\
\062\255\062\255\000\000\114\255\000\000\000\000\240\254\030\255\
\000\000\000\000\119\255\016\255\128\255\000\000\007\255\062\255\
\062\255\062\255\062\255\062\255\062\255\114\255\000\000\062\255\
\062\255\062\255\062\255\062\255\062\255\053\255\000\000\054\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\114\255\007\255\008\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\058\000\000\000\056\255\000\000\
\000\000\000\000\001\255\000\000\000\000\000\000\000\000\047\255\
\000\000\087\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\140\255\000\000\000\000\067\255\000\000\
\000\000\000\000\000\000\000\000\094\255\000\000\060\255\102\255\
\102\255\102\255\102\255\102\255\102\255\140\255\000\000\102\255\
\102\255\102\255\102\255\102\255\102\255\000\000\000\000\061\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\140\255\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\062\000\250\255\213\255\000\000\000\000\000\000\139\000\
\245\255\000\000\000\000"

let yytablesize = 165
let yytable = "\021\000\
\015\000\026\000\063\000\026\000\024\000\026\000\026\000\026\000\
\046\000\026\000\006\000\025\000\001\000\074\000\026\000\026\000\
\046\000\003\000\047\000\026\000\026\000\026\000\026\000\012\000\
\013\000\007\000\072\000\055\000\026\000\009\000\008\000\027\000\
\028\000\057\000\058\000\059\000\060\000\061\000\062\000\010\000\
\019\000\064\000\065\000\066\000\067\000\068\000\069\000\033\000\
\023\000\033\000\026\000\033\000\033\000\033\000\039\000\033\000\
\070\000\001\000\071\000\073\000\033\000\033\000\031\000\035\000\
\036\000\033\000\033\000\034\000\033\000\034\000\020\000\034\000\
\034\000\034\000\000\000\034\000\000\000\011\000\012\000\013\000\
\034\000\034\000\014\000\000\000\000\000\034\000\034\000\032\000\
\034\000\032\000\000\000\000\000\032\000\032\000\008\000\032\000\
\008\000\000\000\000\000\008\000\032\000\032\000\031\000\000\000\
\031\000\032\000\032\000\031\000\032\000\000\000\031\000\000\000\
\000\000\000\000\000\000\031\000\031\000\000\000\000\000\000\000\
\031\000\031\000\000\000\031\000\032\000\033\000\000\000\040\000\
\000\000\011\000\012\000\013\000\041\000\042\000\014\000\000\000\
\048\000\043\000\044\000\000\000\045\000\049\000\050\000\000\000\
\000\000\034\000\051\000\052\000\031\000\053\000\000\000\000\000\
\022\000\031\000\031\000\000\000\000\000\000\000\031\000\031\000\
\000\000\031\000\029\000\030\000\031\000"

let yycheck = "\011\000\
\007\000\001\001\046\000\003\001\021\001\005\001\006\001\007\001\
\001\001\009\001\012\001\028\001\001\000\006\001\014\001\015\001\
\001\001\024\001\003\001\019\001\020\001\021\001\022\001\017\001\
\018\001\027\001\070\000\039\000\028\001\033\001\032\001\003\001\
\004\001\040\000\041\000\042\000\043\000\044\000\045\000\003\001\
\003\001\048\000\049\000\050\000\051\000\052\000\053\000\001\001\
\007\001\003\001\005\001\005\001\006\001\007\001\025\001\009\001\
\004\001\000\000\005\001\071\000\014\001\015\001\007\001\004\001\
\004\001\019\001\020\001\001\001\022\001\003\001\009\000\005\001\
\006\001\007\001\255\255\009\001\255\255\016\001\017\001\018\001\
\014\001\015\001\021\001\255\255\255\255\019\001\020\001\001\001\
\022\001\003\001\255\255\255\255\006\001\007\001\001\001\009\001\
\003\001\255\255\255\255\006\001\014\001\015\001\001\001\255\255\
\003\001\019\001\020\001\006\001\022\001\255\255\009\001\255\255\
\255\255\255\255\255\255\014\001\015\001\255\255\255\255\255\255\
\019\001\020\001\255\255\022\001\011\001\012\001\255\255\009\001\
\255\255\016\001\017\001\018\001\014\001\015\001\021\001\255\255\
\009\001\019\001\020\001\255\255\022\001\014\001\015\001\255\255\
\255\255\032\001\019\001\020\001\009\001\022\001\255\255\255\255\
\014\000\014\001\015\001\255\255\255\255\255\255\019\001\020\001\
\255\255\022\001\024\000\025\000\026\000"

let yynames_const = "\
  AND\000\
  BOOL\000\
  CBRACE\000\
  COLON\000\
  COMMA\000\
  CPAREN\000\
  CSQUARE\000\
  DOT\000\
  EQ\000\
  EOF\000\
  EQEQ\000\
  EXISTS\000\
  FALSE\000\
  FORALL\000\
  GT\000\
  GTE\000\
  LT\000\
  LTE\000\
  MINUS\000\
  NEQ\000\
  NOT\000\
  OBRACE\000\
  OPAREN\000\
  OR\000\
  OSQUARE\000\
  PLUS\000\
  PRINT\000\
  SEMICOLON\000\
  TIMES\000\
  TRUE\000\
  UNION\000\
  "

let yynames_block = "\
  ICONST\000\
  ID\000\
  IDPRIMED\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'relation) in
    Obj.repr(
# 84 "ocparser.mly"
                    (
  _1
)
# 269 "ocparser.ml"
               : Cpure.relation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'relation) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'relation) in
    Obj.repr(
# 89 "ocparser.mly"
                                  (
  UnionRel (_1, _3)
)
# 279 "ocparser.ml"
               : 'relation))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'aexp_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'pconstr) in
    Obj.repr(
# 92 "ocparser.mly"
                                                        (
  BaseRel (_3, _6)
)
# 289 "ocparser.ml"
               : 'relation))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    Obj.repr(
# 95 "ocparser.mly"
                                          (
	BaseRel (_3, mkTrue (get_pos 1))
  )
# 298 "ocparser.ml"
               : 'relation))
; (fun __caml_parser_env ->
    Obj.repr(
# 98 "ocparser.mly"
                     (
	ConstRel true
  )
# 306 "ocparser.ml"
               : 'relation))
; (fun __caml_parser_env ->
    Obj.repr(
# 101 "ocparser.mly"
                      (
	ConstRel false
  )
# 314 "ocparser.ml"
               : 'relation))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'pconstr) in
    Obj.repr(
# 106 "ocparser.mly"
                             ( 
  mkAnd _1 _3 (get_pos 2)
)
# 324 "ocparser.ml"
               : 'pconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'lbconstr) in
    Obj.repr(
# 109 "ocparser.mly"
           ( 
	trans_null (fst _1)
  )
# 333 "ocparser.ml"
               : 'pconstr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'var_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'pconstr) in
    Obj.repr(
# 112 "ocparser.mly"
                                              ( 
	let svars = _3 in
	let qf f v = mkExists [v] f None (get_pos 1) in
	let res = List.fold_left qf _5 svars in
	  res
)
# 346 "ocparser.ml"
               : 'pconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bconstr) in
    Obj.repr(
# 120 "ocparser.mly"
                  ( 
	(fst _1, snd _1)
  )
# 355 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 123 "ocparser.mly"
                        (
	let b, oae = _1 in
	  match oae with
		| Some ae ->
			let tmp = build_relation mkLt ae _3 None (get_pos 2) in
			  (mkAnd b tmp (get_pos 2), Some _3)
		| None -> Err.report_error {Err.error_loc = get_pos 2;
									Err.error_text = "parse error in lhs of <"}
  )
# 371 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 132 "ocparser.mly"
                         (
	let b, oae = _1 in
	  match oae with
		| Some ae ->
			let tmp = build_relation mkLte ae _3 None (get_pos 2) in
			  (mkAnd b tmp (get_pos 2) , Some _3)
		| None -> Err.report_error {Err.error_loc = get_pos 2;
									Err.error_text = "parse error in lhs of <="}
  )
# 387 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 141 "ocparser.mly"
                        (
	let b, oae = _1 in
	  match oae with
		| Some ae ->
			let tmp = build_relation mkGt ae _3 None (get_pos 2) in
			  (mkAnd b tmp (get_pos 2), Some _3)
		| None -> Err.report_error {Err.error_loc = get_pos 2;
									Err.error_text = "parse error in lhs of >"}
)
# 403 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 150 "ocparser.mly"
                         (
	let b, oae = _1 in
	  match oae with
		| Some ae ->
			let tmp = build_relation mkGte ae _3 None (get_pos 2) in
			  (mkAnd b tmp (get_pos 2), Some _3)
		| None -> Err.report_error {Err.error_loc = get_pos 2;
									Err.error_text = "parse error in lhs of >="}
)
# 419 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 159 "ocparser.mly"
                        (
	let b, oae = _1 in
	  match oae with
		| Some ae ->
			let tmp = build_relation mkEq ae _3 None (get_pos 2) in
			  (mkAnd b tmp (get_pos 2), Some _3)
		| None -> Err.report_error {Err.error_loc = get_pos 2;
									Err.error_text = "parse error in lhs of ="}
)
# 435 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lbconstr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 168 "ocparser.mly"
                         (
	let b, oae = _1 in
	  match oae with
		| Some ae ->
			let tmp = build_relation mkNeq ae _3 None (get_pos 2) in
			  (mkAnd b tmp (get_pos 2), Some _3)
		| None -> Err.report_error {Err.error_loc = get_pos 2;
									Err.error_text = "parse error in lhs of !="}
)
# 451 "ocparser.ml"
               : 'lbconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 179 "ocparser.mly"
                                ( (build_relation mkLt _1 _3 None (get_pos 2), Some _3) )
# 459 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 180 "ocparser.mly"
                          ( (build_relation mkLte _1 _3 None (get_pos 2), Some _3) )
# 467 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 181 "ocparser.mly"
                         ( (build_relation mkGt _1 _3 None (get_pos 2), Some _3) )
# 475 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 182 "ocparser.mly"
                          ( (build_relation mkGte _1 _3 None (get_pos 2), Some _3) )
# 483 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 183 "ocparser.mly"
                         ( (build_relation mkEq _1 _3 None (get_pos 2), Some _3) )
# 491 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list) in
    Obj.repr(
# 184 "ocparser.mly"
                          ( (build_relation mkNeq _1 _3 None (get_pos 2), Some _3) )
# 499 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    Obj.repr(
# 185 "ocparser.mly"
       ( (BForm (BConst (true, get_pos 1) , None), None) )
# 505 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    Obj.repr(
# 186 "ocparser.mly"
        ( (BForm (BConst (false, get_pos 1) , None), None) )
# 511 "ocparser.ml"
               : 'bconstr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cid) in
    Obj.repr(
# 189 "ocparser.mly"
          (
	Var (_1,get_pos 1)
  )
# 520 "ocparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 192 "ocparser.mly"
         (
	IConst (_1, get_pos 1)
  )
# 529 "ocparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : int) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'cid) in
    Obj.repr(
# 195 "ocparser.mly"
             (
	Mult (IConst (_1, get_pos 1), (Var (_2,get_pos 2)), get_pos 1)
  )
# 539 "ocparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 198 "ocparser.mly"
                 (
	Add (_1, _3, get_pos 2)
  )
# 549 "ocparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 201 "ocparser.mly"
                  (
	Subtract (_1, _3, get_pos 2)
  )
# 559 "ocparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 204 "ocparser.mly"
                          (
	Subtract (IConst (0, get_pos 1), _2, get_pos 1)
  )
# 568 "ocparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    Obj.repr(
# 209 "ocparser.mly"
           ( [] )
# 574 "ocparser.ml"
               : 'aexp_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aexp_list_rec) in
    Obj.repr(
# 210 "ocparser.mly"
                ( List.rev _1 )
# 581 "ocparser.ml"
               : 'aexp_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 213 "ocparser.mly"
                    ( [_1] )
# 588 "ocparser.ml"
               : 'aexp_list_rec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp_list_rec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 214 "ocparser.mly"
                           ( _3 :: _1)
# 596 "ocparser.ml"
               : 'aexp_list_rec))
; (fun __caml_parser_env ->
    Obj.repr(
# 217 "ocparser.mly"
          ( [] : spec_var list )
# 602 "ocparser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var_list_rec) in
    Obj.repr(
# 218 "ocparser.mly"
               ( List.rev _1 : spec_var list )
# 609 "ocparser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'cid) in
    Obj.repr(
# 221 "ocparser.mly"
                  ( ([_1]) : spec_var list )
# 616 "ocparser.ml"
               : 'var_list_rec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var_list_rec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cid) in
    Obj.repr(
# 222 "ocparser.mly"
                         ( (_3 :: _1) : spec_var list )
# 624 "ocparser.ml"
               : 'var_list_rec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 226 "ocparser.mly"
        ( match (List.filter (fun (a,b,_)->((String.compare _1 a)==0)) !subst_lst) with 
					|  [] -> SpecVar(Prim Int,_1, Unprimed)
					| (a,b,t)::h-> SpecVar(t, b,Unprimed) )
# 633 "ocparser.ml"
               : 'cid))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 229 "ocparser.mly"
           ( match (List.filter (fun (a,b,_)->((String.compare _1 a)==0)) !subst_lst) with 
					|  [] -> SpecVar(Prim Int,_1, Primed)
					| (a,b,t)::h-> SpecVar(t, b,Primed) )
# 642 "ocparser.ml"
               : 'cid))
(* Entry oc_output *)
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
let oc_output (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Cpure.relation)
