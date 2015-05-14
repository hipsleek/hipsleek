%{
(* Modified from https://github.com/mmjb/T2/blob/master/src/absparse.fsy *)
(* //                                                                              *)
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

open Globals
open Iast

(* ///                                                    *)
(* /// Location in a T2 file (either numerical or a name) *)
(* ///                                                    *)
type parsedLoc =
  | NumLoc of int
  | NameLoc of string

%}

%token <string> ID
%token <int> NUM
%token AT
%token SEMICOLON COLON COMMA
%token EOF
%token LPAREN RPAREN
%token DIV REM STAR PLUS MINUS 
%token EQ GE GT LE LT NE NOT 
%token AND_OP OR_OP
%token ASSUME ASSIGN NONDET SHADOW
%token TO FROM CUTPOINT START
(* %token AF AG AW AX EF EG EU EX *)

%start program
(* %start CTL_formula         *)
(* %start Fairness_constraint *)

%left OR_OP
%left AND_OP
%left PLUS MINUS
%left STAR DIV REM
%left UMINUS


%%


program:
    START COLON loc SEMICOLON CUTPOINT COLON loc SEMICOLON shadows blocks 
    { None }
  | START COLON loc SEMICOLON shadows blocks 
    { None }

blocks: 
    { [] }
  | block SEMICOLON blocks { $1::$3 }

block: 
  FROM COLON loc SEMICOLON commands TO COLON loc { None }

shadows: 
    { [] }
  | shadow SEMICOLON shadows { $1::$3 }

shadow: 
  SHADOW LPAREN Id COMMA Id RPAREN { ($3, $5) }

commands: 
    { [] }
  | command SEMICOLON commands { $1::$3 }

loc:
    NUM { NumLoc $1 }
  | ID { NameLoc $1 }

command: 
    AT LPAREN Num COMMA String RPAREN Id ASSIGN term
    { None }
  | AT LPAREN Num COMMA String RPAREN ASSUME LPAREN formula RPAREN
    { None }
  | AT LPAREN Num COMMA String RPAREN ASSUME LPAREN term RPAREN
    { None }
  | ID ASSIGN term
    { None }
  | ASSUME LPAREN formula RPAREN
    { None }
  | ASSUME LPAREN term RPAREN
    { None}
  ;

term: 
    NUM { None }
  | MINUS term %prec UMINUS { None }
  | ID { None }
  | LPAREN term RPAREN { None }
  | term PLUS term { None }
  | term MINUS term { None }
  | term STAR term { None }
  | term REM term { None }
  | term DIV term { None }
  | NONDET LPAREN RPAREN { None }
  ;

formula: 
    term LT term { None }
  | term GT term { None }
  | term LE term { None }
  | term GE term { None }
  | term EQ term { None }
  | term NE term { None }
  | NOT formula { None }
  | formula AND_OP formula { None }
  | formula OR_OP formula { None }
  | LPAREN formula RPAREN { None }
  ;