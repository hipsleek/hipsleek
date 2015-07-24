%{
(* Modified from https://github.com/mmjb/T2/blob/master/src/absparse.fsy *)

(* // Copyright (c) Microsoft Corporation                                          *)
(* //                                                                              *)
(* // All rights reserved.                                                         *)
(* //                                                                              *)
(* // Permission is hereby granted, free of charge, to any person obtaining a copy *)
(* // of this software and associated documentation files (the ""Software""), to   *)
(* // deal in the Software without restriction, including without limitation the   *)
(* // rights to use, copy, modify, merge, publish, distribute, sublicense, and/or  *)
(* // sell copies of the Software, and to permit persons to whom the Software is   *)
(* // furnished to do so, subject to the following conditions:                     *)
(* //                                                                              *)
(* // The above copyright notice and this permission notice shall be included      *)
(* // in all copies or substantial portions of the Software.                       *)
(* //                                                                              *)
(* // THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR   *)
(* // IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,     *)
(* // FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL      *)
(* // THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER   *)
(* // LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING      *)
(* // FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER          *)
(* // DEALINGS IN THE SOFTWARE.                                                    *)

open VarGen
open Globals
open Iast
open Iexp

(* ///                                                    *)
(* /// Location in a T2 file (either numerical or a name) *)
(* ///                                                    *)

let get_pos x =
  try
    let sp = Parsing.symbol_start_pos () in
    let ep = Parsing. symbol_end_pos () in
    let mp = Parsing.rhs_start_pos x in
    { start_pos = sp;
      end_pos = ep;
      mid_pos = mp; }
  with _ -> 
    { start_pos = Lexing.dummy_pos;
      end_pos = Lexing.dummy_pos;
      mid_pos = Lexing.dummy_pos; }

%}

%token <string> Id
%token <string> String
%token <int> Num
%token AT
%token SEMICOLON COLON COMMA
%token EOF
%token LPAREN RPAREN
%token DIV REM STAR PLUS MINUS 
%token EQ GE GT LE LT NE NOT 
%token AND_OP OR_OP
%token ASSUME ASSIGN NONDET SHADOW
%token TO FROM CUTPOINT START

%start program
%type <Iexp.ints_prog> program

%left OR_OP
%left AND_OP
%left PLUS MINUS
%left STAR DIV REM
%left UMINUS


%%


program:
    START COLON loc SEMICOLON CUTPOINT COLON loc SEMICOLON shadows blocks 
    { mkProg $3 $10 }
  | START COLON loc SEMICOLON shadows blocks 
    { mkProg $3 $6 }

blocks: 
    { [] }
  | block SEMICOLON blocks { $1::$3 }

block: 
  FROM COLON loc SEMICOLON commands TO COLON loc 
  { mkBlock $3 $8 $5 (get_pos 1) }

shadows: 
    { [] }
  | shadow SEMICOLON shadows { $1::$3 }

shadow: 
  SHADOW LPAREN Id COMMA Id RPAREN { ($3, $5) }

commands: 
    { [] }
  | command SEMICOLON commands { $1::$3 }

loc:
    Num { NumLoc ($1, get_pos 1) }
  | Id { NameLoc ($1, get_pos 1) }

command: 
    AT LPAREN Num COMMA String RPAREN Id ASSIGN term
    { mkAssign (mkVar $7 (get_pos 7)) $9 (get_pos 8) }
  | AT LPAREN Num COMMA String RPAREN ASSUME LPAREN formula RPAREN
    { mkAssume $9 (get_pos 7) }
  | AT LPAREN Num COMMA String RPAREN ASSUME LPAREN term RPAREN
    { mkAssume $9 (get_pos 7) }
  | Id ASSIGN term
    { mkAssign (mkVar $1 (get_pos 1)) $3 (get_pos 2) }
  | ASSUME LPAREN formula RPAREN
    { mkAssume $3 (get_pos 1) }
  | ASSUME LPAREN term RPAREN
    { mkAssume $3 (get_pos 1) }
  ;

term: 
    Num 
    { mkIntLit $1 (get_pos 1) }
  | MINUS term %prec UMINUS 
    {
      let zero = mkIntLit 0 (get_pos 1) in
      mkBinary OpMinus zero $2 (fresh_branch_point_id "") (get_pos 1)
    }
  | Id 
    { mkVar $1 (get_pos 1) }
  | LPAREN term RPAREN { $2 }
  | term PLUS term 
    { mkBinary OpPlus $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term MINUS term 
    { mkBinary OpMinus $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term STAR term 
    { mkBinary OpMult $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term REM term
    { mkBinary OpMod $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term DIV term 
    { mkBinary OpDiv $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | NONDET LPAREN RPAREN 
    {
      let pn = nondet_int_proc_name in
      let () = Hashtbl.add tnt_prim_proc_tbl pn pn in 
      mkCallNRecv pn None [] None (fresh_branch_point_id "") (get_pos 1) 
    }
  ;

formula: 
    term LT term 
    { mkBinary OpLt $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term GT term
    { mkBinary OpGt $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term LE term 
    { mkBinary OpLte $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term GE term 
    { mkBinary OpGte $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term EQ term 
    { mkBinary OpEq $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | term NE term 
    { mkBinary OpNeq $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | NOT formula 
    { mkUnary OpNot $2 (fresh_branch_point_id "") (get_pos 1) }
  | formula AND_OP formula 
    { mkBinary OpLogicalAnd $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | formula OR_OP formula
    { mkBinary OpLogicalOr $1 $3 (fresh_branch_point_id "") (get_pos 2) }
  | LPAREN formula RPAREN { $2 }
  ;