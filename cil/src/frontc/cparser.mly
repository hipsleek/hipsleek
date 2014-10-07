/*(*
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 **)
(**
** 1.0	3.22.99	Hugues Cass�	First version.
** 2.0  George Necula 12/12/00: Practically complete rewrite.
*)
*/
%{
open Cabs
open Cabshelper
module E = Errormsg

let parse_error msg : unit =       (* sm: c++-mode highlight hack: -> ' <- *)
  E.parse_error msg

let print = print_string

(* unit -> string option *)
(*
let getComments () =
  match !comments with
    [] -> None
  | _ -> 
      let r = Some(String.concat "\n" (List.rev !comments)) in
      comments := [];
      r
*)

(* cabsloc -> cabsloc *)
(*
let handleLoc l =
  l.clcomment <- getComments();
  l
*)

(*
** Expression building
*)
let smooth_expression lst loc =
  match lst with
    [] -> NOTHING
  | [expr] -> expr
  | _ -> COMMA (lst, loc)


let currentFunctionName = ref "<outside any function>"
    
let announceFunctionName ((n, decl, _, _):name) =
  !Lexerhack.add_identifier n;
  (* Start a context that includes the parameter names and the whole body. 
   * Will pop when we finish parsing the function body *)
  !Lexerhack.push_context ();
  (* Go through all the parameter names and mark them as identifiers *)
  let rec findProto = function
      PROTO (d, args, _) when isJUSTBASE d -> 
        List.iter (fun (_, (an, _, _, _)) -> !Lexerhack.add_identifier an) args

    | PROTO (d, _, _) -> findProto d
    | PARENTYPE (_, d, _) -> findProto d
    | PTR (_, d) -> findProto d
    | ARRAY (d, _, _) -> findProto d
    | _ -> parse_error "Cannot find the prototype in a function definition";
           raise Parsing.Parse_error 

  and isJUSTBASE = function
      JUSTBASE -> true
    | PARENTYPE (_, d, _) -> isJUSTBASE d
    | _ -> false
  in
  findProto decl;
  currentFunctionName := n



let applyPointer (ptspecs: attribute list list) (dt: decl_type)  
       : decl_type = 
  (* Outer specification first *)
  let rec loop = function
      [] -> dt
    | attrs :: rest -> PTR(attrs, loop rest)
  in
  loop ptspecs

let doDeclaration (loc: cabsloc) (specs: spec_elem list) (nl: init_name list) : definition = 
  if isTypedef specs then begin
    (* Tell the lexer about the new type names *)
    List.iter (fun ((n, _, _, _), _) -> !Lexerhack.add_type n) nl;
    TYPEDEF ((specs, List.map (fun (n, _) -> n) nl), loc)
  end else
    if nl = [] then
      ONLYTYPEDEF (specs, loc)
    else begin
      (* Tell the lexer about the new variable names *)
      List.iter (fun ((n, _, _, _), _) -> !Lexerhack.add_identifier n) nl;
      DECDEF ((specs, nl), loc)  
    end


let doFunctionDef (loc: cabsloc)
                  (specs: spec_elem list) 
                  (n: name)
                  (hs: hip_func_spec)
                  (b: block) : definition = 
  let fname = (specs, n) in
  FUNDEF (fname, hs, b, loc)


let doOldParDecl (names: string list)
                 ((pardefs: name_group list), (isva: bool)) 
    : single_name list * bool =
  let findOneName n =
    (* Search in pardefs for the definition for this parameter *)
    let rec loopGroups = function
        [] -> ([SpecType Tint], (n, JUSTBASE, [], cabslu))
      | (specs, names) :: restgroups ->
          let rec loopNames = function
              [] -> loopGroups restgroups
            | ((n',_, _, _) as sn) :: _ when n' = n -> (specs, sn)
            | _ :: restnames -> loopNames restnames
          in
          loopNames names
    in
    loopGroups pardefs
  in
  let args = List.map findOneName names in
  (args, isva)

let checkConnective (s : string) : unit =
begin
  (* checking this means I could possibly have more connectives, with *)
  (* different meaning *)
  if (s <> "to") then (
    parse_error "transformer connective must be 'to'";
    raise Parsing.Parse_error
  )
  else ()
end

let int64_to_char value =
  if (compare value (Int64.of_int 255) > 0) || (compare value Int64.zero < 0) then
    begin
      let msg = Printf.sprintf "cparser:intlist_to_string: character 0x%Lx too big" value in
      parse_error msg;
      raise Parsing.Parse_error
    end
  else
    Char.chr (Int64.to_int value)

(* takes a not-nul-terminated list, and converts it to a string. *)
let rec intlist_to_string (str: int64 list):string =
  match str with
    [] -> ""  (* add nul-termination *)
  | value::rest ->
      let this_char = int64_to_char value in
      (String.make 1 this_char) ^ (intlist_to_string rest)

let fst3 (result, _, _) = result
let snd3 (_, result, _) = result
let trd3 (_, _, result) = result

let fst4 (result, _, _, _) = result
let snd4 (_, result, _, _) = result
let trd4 (_, _, result, _) = result
let fth4 (_, _, _, result) = result


(* TRUNG TODO: check location in this function *)
(*
   transform:  __builtin_offsetof(type, member)
   into     :  (size_t) (&(type * ) 0)->member
 *)
let transformOffsetOf (speclist, dtype) member loc =
  let rec addPointer = function
    | JUSTBASE -> PTR([], JUSTBASE)
    | PARENTYPE (attrs1, dtype, attrs2) -> PARENTYPE (attrs1, addPointer dtype, attrs2)
    | ARRAY (dtype, attrs, expr) -> ARRAY (addPointer dtype, attrs, expr)
    | PTR (attrs, dtype) -> PTR (attrs, addPointer dtype)
    | PROTO (dtype, names, variadic) -> PROTO (addPointer dtype, names, variadic)
  in
  let nullType = (speclist, addPointer dtype) in
  let nullExpr = CONSTANT (CONST_INT "0", cabslu) in
  let castExpr = CAST (nullType, SINGLE_INIT nullExpr, cabslu) in

  let rec replaceBase = function
    | VARIABLE (field, l) -> MEMBEROFPTR (castExpr, field, l)
    | MEMBEROF (base, field, l) -> MEMBEROF (replaceBase base, field, l)
    | INDEX (base, index, l) -> INDEX (replaceBase base, index, l)
    | _ ->
        parse_error "malformed offset expression in __builtin_offsetof";
        raise Parsing.Parse_error 
  in
  let memberExpr = replaceBase member in
  let addrExpr = UNARY (ADDROF, memberExpr, loc) in
  (* slight cheat: hard-coded assumption that size_t == unsigned int *)
  let sizeofType = ([SpecType Tunsigned], JUSTBASE) in
  let resultExpr = CAST (sizeofType, SINGLE_INIT addrExpr, loc) in
  resultExpr

%}

%token <string * Cabs.cabsloc> IDENT
%token <string * Cabs.cabsloc> QUALIFIER
%token <int64 list * Cabs.cabsloc> CST_CHAR
%token <int64 list * Cabs.cabsloc> CST_WCHAR
%token <string * Cabs.cabsloc> CST_INT
%token <string * Cabs.cabsloc> CST_FLOAT
%token <string * Cabs.cabsloc> NAMED_TYPE
%token <string * Cabs.cabsloc> HIPSPEC                       /* hip specification */

/* Each character is its own list element, and the terminating nul is not
   included in this list. */
%token <int64 list * Cabs.cabsloc> CST_STRING   
%token <int64 list * Cabs.cabsloc> CST_WSTRING

%token EOF
%token<Cabs.cabsloc> CHAR INT BOOL DOUBLE FLOAT VOID INT64 INT32
%token<Cabs.cabsloc> ENUM STRUCT TYPEDEF UNION
%token<Cabs.cabsloc> SIGNED UNSIGNED LONG SHORT
%token<Cabs.cabsloc> VOLATILE EXTERN STATIC CONST RESTRICT AUTO REGISTER
%token<Cabs.cabsloc> THREAD

%token<Cabs.cabsloc> SIZEOF ALIGNOF

%token<Cabs.cabsloc> EQ PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ PERCENT_EQ
%token<Cabs.cabsloc> AND_EQ PIPE_EQ CIRC_EQ INF_INF_EQ SUP_SUP_EQ
%token<Cabs.cabsloc> ARROW DOT

%token<Cabs.cabsloc> EQ_EQ EXCLAM_EQ INF SUP INF_EQ SUP_EQ
%token<Cabs.cabsloc> PLUS MINUS STAR
%token<Cabs.cabsloc> SLASH PERCENT
%token<Cabs.cabsloc> TILDE AND
%token<Cabs.cabsloc> PIPE CIRC
%token<Cabs.cabsloc> EXCLAM AND_AND
%token<Cabs.cabsloc> PIPE_PIPE
%token<Cabs.cabsloc> INF_INF SUP_SUP
%token<Cabs.cabsloc> PLUS_PLUS MINUS_MINUS

%token<Cabs.cabsloc> RPAREN 
%token<Cabs.cabsloc> LPAREN RBRACE
%token<Cabs.cabsloc> LBRACE
%token<Cabs.cabsloc> LBRACKET RBRACKET
%token<Cabs.cabsloc> COLON
%token<Cabs.cabsloc> SEMICOLON
%token<Cabs.cabsloc> COMMA ELLIPSIS QUEST

%token<Cabs.cabsloc> BREAK CONTINUE GOTO RETURN
%token<Cabs.cabsloc> SWITCH CASE DEFAULT
%token<Cabs.cabsloc> WHILE DO FOR
%token<Cabs.cabsloc> IF TRY EXCEPT FINALLY
%token<Cabs.cabsloc> ELSE 

%token<Cabs.cabsloc> ATTRIBUTE INLINE ASM TYPEOF FUNCTION__ PRETTY_FUNCTION__
%token<Cabs.cabsloc> LABEL__
%token<Cabs.cabsloc> BUILTIN_VA_ARG ATTRIBUTE_USED
%token<Cabs.cabsloc> BUILTIN_VA_LIST
%token<Cabs.cabsloc> BLOCKATTRIBUTE 
%token<Cabs.cabsloc> BUILTIN_TYPES_COMPAT BUILTIN_OFFSETOF
%token<Cabs.cabsloc> DECLSPEC
%token<string * Cabs.cabsloc> MSASM MSATTR
%token<string * Cabs.cabsloc> PRAGMA_LINE
%token<Cabs.cabsloc> PRAGMA
%token<Cabs.cabsloc> PRAGMA_EOL

/* sm: cabs tree transformation specification keywords */
%token<Cabs.cabsloc> AT_TRANSFORM AT_TRANSFORMEXPR AT_SPECIFIER AT_EXPR
%token<Cabs.cabsloc> AT_NAME

/* operator precedence */
%nonassoc 	IF
%nonassoc 	ELSE


%left   COMMA
%right  EQ PLUS_EQ MINUS_EQ STAR_EQ SLASH_EQ PERCENT_EQ
        AND_EQ PIPE_EQ CIRC_EQ INF_INF_EQ SUP_SUP_EQ
%right  QUEST COLON
%left   PIPE_PIPE
%left   AND_AND
%left   PIPE
%left   CIRC
%left   AND
%left   EQ_EQ EXCLAM_EQ
%left   INF SUP INF_EQ SUP_EQ
%left   INF_INF SUP_SUP
%left   PLUS MINUS
%left   STAR SLASH PERCENT CONST RESTRICT VOLATILE
%right  EXCLAM TILDE PLUS_PLUS MINUS_MINUS CAST RPAREN ADDROF SIZEOF ALIGNOF
%left   LBRACKET
%left   DOT ARROW LPAREN LBRACE
%right  NAMED_TYPE     /* We'll use this to handle redefinitions of
                        * NAMED_TYPE as variables */
%left   IDENT

/* Non-terminals informations */
%start interpret file
%type <Cabs.definition list> file interpret

%type <Cabs.definition list * cabsloc> globals
%type <Cabs.definition * cabsloc> global

%type <Cabs.attribute list * cabsloc> attributes attributes_with_asm asmattr
%type <Cabs.statement * cabsloc> statement
%type <Cabs.constant * cabsloc> constant
%type <string * cabsloc> string_constant
%type <Cabs.expression * cabsloc> expression
%type <Cabs.expression * cabsloc> opt_expression
%type <Cabs.init_expression * cabsloc> init_expression
%type <Cabs.expression list * cabsloc> comma_expression
%type <Cabs.expression list * cabsloc> paren_comma_expression
%type <Cabs.expression list * cabsloc> arguments
%type <Cabs.expression list * cabsloc> bracket_comma_expression
%type <int64 list Queue.t * cabsloc> string_list 
%type <int64 list * cabsloc> wstring_list

%type <(Cabs.initwhat * Cabs.init_expression) * cabsloc> initializer
%type <(Cabs.initwhat * Cabs.init_expression) list * cabsloc> initializer_list
%type <Cabs.initwhat * cabsloc> init_designators init_designators_opt

%type <spec_elem list * cabsloc> decl_spec_list
%type <typeSpecifier * cabsloc> type_spec
%type <Cabs.field_group list * cabsloc> struct_decl_list


%type <Cabs.name * cabsloc> old_proto_decl
%type <Cabs.single_name * cabsloc> parameter_decl
%type <Cabs.enum_item * cabsloc> enumerator
%type <Cabs.enum_item list * cabsloc> enum_list
%type <Cabs.definition * cabsloc> declaration function_def
%type <spec_elem list * name * cabsloc> function_def_start
%type <Cabs.spec_elem list * Cabs.decl_type * cabsloc> type_name
%type <Cabs.block * cabsloc> block
%type <Cabs.statement list * cabsloc> block_element_list
%type <string list * cabsloc> local_labels local_label_names
%type <string list * cabsloc> old_parameter_list_ne

%type <Cabs.init_name * cabsloc> init_declarator
%type <Cabs.init_name list * cabsloc> init_declarator_list
%type <Cabs.name * cabsloc> declarator
%type <(Cabs.name * expression option) * cabsloc> field_decl
%type <(Cabs.name * expression option) list * cabsloc> field_decl_list
%type <string * Cabs.decl_type * cabsloc> direct_decl
%type <Cabs.decl_type * cabsloc> abs_direct_decl abs_direct_decl_opt
%type <Cabs.decl_type * Cabs.attribute list * cabsloc> abstract_decl

 /* (* Each element is a "* <type_quals_opt>". *) */
%type <attribute list list * cabsloc> pointer pointer_opt
%type <Cabs.cabspos> position
%type <Cabs.spec_elem * cabsloc> cvspec
%%

interpret:
  file EOF                              { $1 }
;

file:
  globals                               { fst $1 }
;

globals:
  /* empty */                           { [], currentLoc () }
| global globals                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
| SEMICOLON globals                     { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          fst $2, loc }
;

position:
  /* empty */                           { currentPos () }  %prec IDENT

/*** Global Definition ***/
global:
| declaration                           { $1 }
| function_def                          { $1 } 
/*(* Some C header files ar shared with the C++ compiler and have linkage 
   * specification *)*/
| EXTERN string_constant declaration    { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          (LINKAGE (fst $2, loc, [fst $3]), loc) }
| EXTERN string_constant LBRACE globals RBRACE 
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          (LINKAGE (fst $2, loc, fst $4), loc) }
| ASM LPAREN string_constant RPAREN SEMICOLON
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          (GLOBASM (fst $3, loc), loc) }
| pragma                                { $1 }
/* (* Old-style function prototype. This should be somewhere else, like in
    * "declaration". For now we keep it at global scope only because in local
    * scope it looks too much like a function call  *) */
| IDENT LPAREN old_parameter_list_ne RPAREN old_pardef_list SEMICOLON
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $6) in
                                          (* Convert pardecl to new style *)
                                          let pardecl, isva = doOldParDecl (fst $3) (fst $5) in
                                          let loc1 = makeLoc (startPos $2) (endPos (snd $5)) in
                                          (* Make the function declarator *)
                                          (doDeclaration loc []
                                            [((fst $1, PROTO(JUSTBASE, pardecl,isva), [], loc1),
                                              NO_INIT)], loc) }
/* (* Old style function prototype, but without any arguments *) */
| IDENT LPAREN RPAREN  SEMICOLON        { let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          (* Make the function declarator *)
                                          let loc1 = makeLoc (startPos $2) (endPos $3) in
                                          (doDeclaration loc []
                                            [((fst $1, PROTO(JUSTBASE,[],false), [], loc1),
                                              NO_INIT)], loc) }
/* transformer for a toplevel construct */
| AT_TRANSFORM LBRACE global RBRACE  IDENT/*to*/  LBRACE globals RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $8) in
                                          checkConnective(fst $5);
                                          (TRANSFORMER(fst $3, fst $7, $1), loc) }
/* transformer for an expression */
| AT_TRANSFORMEXPR LBRACE expression RBRACE  IDENT/*to*/  LBRACE expression RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $8) in
                                          checkConnective(fst $5);
                                          (EXPRTRANSFORMER(fst $3, fst $7, $1), loc) }
| HIPSPEC                               { let spec, loc = $1 in
                                          (HIP_PROG_SPEC (spec, loc), loc) }
| position error position SEMICOLON     { let loc = makeLoc $1 (endPos $4) in
                                          let loc1 = makeLoc $1 $3 in
                                          (PRAGMA (VARIABLE ("parse_error", loc1), loc), loc) }
;

id_or_typename:
  IDENT                                 { $1 }
| NAMED_TYPE                            { $1 }
| AT_NAME LPAREN IDENT RPAREN           { let loc = makeLoc (startPos $1) (endPos $4) in
                                          ("@name(" ^ fst $3 ^ ")", loc) }     /* pattern variable name */
;

maybecomma:
  /* empty */                           { (), currentLoc () }
| COMMA                                 { (), $1 }
;

/* *** Expressions *** */

primary_expression:                     /*(* 6.5.1. *)*/
| IDENT                                 { VARIABLE (fst $1, snd $1), snd $1 }
| constant                              { CONSTANT (fst $1, snd $1), snd $1 }
| paren_comma_expression                { let es, loc = $1 in
                                          PAREN (smooth_expression es loc, loc), loc }
| LPAREN block RPAREN                   { let loc = makeLoc (startPos $1) (endPos $3) in
                                          GNU_BODY (fst $2, loc), loc }
     /*(* Next is Scott's transformer *)*/
| AT_EXPR LPAREN IDENT RPAREN         /* expression pattern variable */
                                        { let loc = makeLoc (startPos $1) (endPos $4) in
                                          EXPR_PATTERN(fst $3, loc), loc }
;

postfix_expression:                     /*(* 6.5.2 *)*/
| primary_expression                    { $1 }
| postfix_expression bracket_comma_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          INDEX (fst $1, smooth_expression (fst $2) (snd $2), loc), loc }
| postfix_expression LPAREN arguments RPAREN
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          CALL (fst $1, fst $3, loc), loc }
| BUILTIN_VA_ARG LPAREN expression COMMA type_name RPAREN
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          let b, d, loc1 = $5 in
                                          CALL (VARIABLE ("__builtin_va_arg", $1), 
                                                [fst $3; TYPE_SIZEOF (b, d, loc1)], loc), loc }
| BUILTIN_TYPES_COMPAT LPAREN type_name COMMA type_name RPAREN
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          let b1,d1,loc1 = $3 in
                                          let b2,d2,loc2 = $5 in
                                          CALL (VARIABLE ("__builtin_types_compatible_p", $1), 
                                                [TYPE_SIZEOF(b1,d1,loc1); TYPE_SIZEOF(b2,d2,loc2)], loc), loc }
| BUILTIN_OFFSETOF LPAREN type_name COMMA offsetof_member_designator RPAREN
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          transformOffsetOf (fst3 $3, snd3 $3) (fst $5) loc, loc }
| postfix_expression DOT id_or_typename { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          MEMBEROF (fst $1, fst $3, loc), loc}
| postfix_expression ARROW id_or_typename
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          MEMBEROFPTR (fst $1, fst $3, loc), loc}
| postfix_expression PLUS_PLUS          { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          UNARY (POSINCR, fst $1, loc), loc}
| postfix_expression MINUS_MINUS        { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          UNARY (POSDECR, fst $1, loc), loc}
/* (* We handle GCC constructor expressions *) */
| LPAREN type_name RPAREN LBRACE initializer_list_opt RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          CAST((fst3 $2, snd3 $2), COMPOUND_INIT (fst $5), loc), loc }
;

offsetof_member_designator:  /* GCC extension for __builtin_offsetof */
| id_or_typename                        { VARIABLE (fst $1, snd $1), snd $1 }
| offsetof_member_designator DOT IDENT  { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          MEMBEROF (fst $1, fst $3, loc), loc }
| offsetof_member_designator bracket_comma_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          INDEX (fst $1, smooth_expression (fst $2) (snd $2), loc), loc }
;

unary_expression:   /*(* 6.5.3 *)*/
| postfix_expression                    { $1 }
| PLUS_PLUS unary_expression            { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (PREINCR, fst $2, loc), loc }
| MINUS_MINUS unary_expression          { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (PREDECR, fst $2, loc), loc }
| SIZEOF unary_expression               { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          EXPR_SIZEOF (fst $2, loc), loc }
| SIZEOF LPAREN type_name RPAREN        { let loc = makeLoc (startPos $1) (endPos $4) in
                                          let b, d, _ = $3 in
                                          TYPE_SIZEOF (b, d, loc), loc }
| ALIGNOF unary_expression              { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          EXPR_ALIGNOF (fst $2, loc), loc }
| ALIGNOF LPAREN type_name RPAREN       { let loc = makeLoc (startPos $1) (endPos $4) in
                                          let b, d, _ = $3 in
                                          TYPE_ALIGNOF (b, d, loc), loc }
| PLUS cast_expression                  { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (PLUS, fst $2, loc), loc }
| MINUS cast_expression                 { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (MINUS, fst $2, loc), loc }
| STAR cast_expression                  { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (MEMOF, fst $2, loc), loc }
| AND cast_expression                   { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (ADDROF, fst $2, loc), loc }
| EXCLAM cast_expression                { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (NOT, fst $2, loc), loc }
| TILDE cast_expression                 { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (BNOT, fst $2, loc), loc }
| AND_AND IDENT                         { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          LABELADDR (fst $2, loc), loc }
;

cast_expression:   /*(* 6.5.4 *)*/
| unary_expression                      { $1 }
| LPAREN type_name RPAREN cast_expression
                                        { let loc = makeLoc (startPos $1) (endPos (snd $4)) in
                                          CAST((fst3 $2, snd3 $2), SINGLE_INIT (fst $4), loc), loc }
;

multiplicative_expression:  /*(* 6.5.5 *)*/
| cast_expression                       { $1 }
| multiplicative_expression STAR cast_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(MUL, fst $1, fst $3, loc), loc }
| multiplicative_expression SLASH cast_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(DIV, fst $1, fst $3, loc), loc }
| multiplicative_expression PERCENT cast_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(MOD, fst $1, fst $3, loc), loc }
;

additive_expression:  /*(* 6.5.6 *)*/
| multiplicative_expression             { $1 }
| additive_expression PLUS multiplicative_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(ADD, fst $1, fst $3, loc), loc }
| additive_expression MINUS multiplicative_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SUB, fst $1, fst $3, loc), loc }
;

shift_expression:      /*(* 6.5.7 *)*/
| additive_expression                   { $1 }
| shift_expression  INF_INF additive_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SHL, fst $1, fst $3, loc), loc }
| shift_expression  SUP_SUP additive_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SHR, fst $1, fst $3, loc), loc }
;

relational_expression:   /*(* 6.5.8 *)*/
| shift_expression                      { $1 }
| relational_expression INF shift_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(LT, fst $1, fst $3, loc), loc }
| relational_expression SUP shift_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(GT, fst $1, fst $3, loc), loc }
| relational_expression INF_EQ shift_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(LE, fst $1, fst $3, loc), loc }
| relational_expression SUP_EQ shift_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(GE, fst $1, fst $3, loc), loc }
;

equality_expression:   /*(* 6.5.9 *)*/
| relational_expression                 { $1 }
| equality_expression EQ_EQ relational_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(EQ, fst $1, fst $3, loc), loc }
| equality_expression EXCLAM_EQ relational_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(NE, fst $1, fst $3, loc), loc }
;


bitwise_and_expression:   /*(* 6.5.10 *)*/
| equality_expression                   { $1 }
| bitwise_and_expression AND equality_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(BAND, fst $1, fst $3, loc), loc }
;

bitwise_xor_expression:   /*(* 6.5.11 *)*/
| bitwise_and_expression                { $1 }
| bitwise_xor_expression CIRC bitwise_and_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(XOR, fst $1, fst $3, loc), loc }
;

bitwise_or_expression:   /*(* 6.5.12 *)*/
| bitwise_xor_expression                { $1 } 
| bitwise_or_expression PIPE bitwise_xor_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(BOR, fst $1, fst $3, loc), loc }
;

logical_and_expression:   /*(* 6.5.13 *)*/
| bitwise_or_expression                 { $1 }
| logical_and_expression AND_AND bitwise_or_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(AND, fst $1, fst $3, loc), loc }
;

logical_or_expression:   /*(* 6.5.14 *)*/
| logical_and_expression                { $1 }
| logical_or_expression PIPE_PIPE logical_and_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(OR, fst $1, fst $3, loc), loc }
;

conditional_expression:    /*(* 6.5.15 *)*/
| logical_or_expression                 { $1 }
| logical_or_expression QUEST opt_expression COLON conditional_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $5)) in
                                          QUESTION (fst $1, fst $3, fst $5, loc), loc }
;

/*(* The C spec says that left-hand sides of assignment expressions are unary 
 * expressions. GCC allows cast expressions in there ! *)*/

assignment_expression:     /*(* 6.5.16 *)*/
| conditional_expression                { $1 }
| cast_expression EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression PLUS_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(ADD_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression MINUS_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SUB_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression STAR_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(MUL_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression SLASH_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(DIV_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression PERCENT_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(MOD_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression AND_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(BAND_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression PIPE_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(BOR_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression CIRC_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(XOR_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression INF_INF_EQ assignment_expression  
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SHL_ASSIGN, fst $1, fst $3, loc), loc }
| cast_expression SUP_SUP_EQ assignment_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SHR_ASSIGN, fst $1, fst $3, loc), loc }
;

expression:           /*(* 6.5.17 *)*/
  assignment_expression                 { $1 }
;

constant:
  CST_INT                               { CONST_INT (fst $1), snd $1 }
| CST_FLOAT                             { CONST_FLOAT (fst $1), snd $1 }
| CST_CHAR                              { CONST_CHAR (fst $1), snd $1 }
| CST_WCHAR                             { CONST_WCHAR (fst $1), snd $1 }
| string_constant                       { CONST_STRING (fst $1), snd $1 }
| wstring_list                          { CONST_WSTRING (fst $1), snd $1 }
;

string_constant:
  /* Now that we know this constant isn't part of a wstring, convert it
     back to a string for easy viewing. */
  string_list                           { let queue, location = $1 in
                                          let buffer = Buffer.create (Queue.length queue) in
                                          Queue.iter (
                                            List.iter (fun value ->
                                              let char = int64_to_char value in
                                              Buffer.add_char buffer char)
                                          ) queue;
                                          Buffer.contents buffer, location }
;

one_string_constant:
  /* Don't concat multiple strings.  For asm templates. */
  CST_STRING                            { intlist_to_string (fst $1), snd $1 }
;

string_list:
  one_string                            { let queue = Queue.create () in
                                          Queue.add (fst $1) queue;
                                          queue, snd $1 }
| string_list one_string                { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          Queue.add (fst $2) (fst $1);
                                          (fst $1), loc }
;

wstring_list:
  CST_WSTRING                           { $1 }
| wstring_list one_string               { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) @ (fst $2), loc }
| wstring_list CST_WSTRING              { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) @ (fst $2), loc }
/* Only the first string in the list needs an L, so L"a" "b" is the same
 * as L"ab" or L"a" L"b". */

one_string: 
  CST_STRING                            { $1 }
| FUNCTION__                            { (Cabshelper.explodeStringToInts !currentFunctionName), $1 }
| PRETTY_FUNCTION__                     { (Cabshelper.explodeStringToInts !currentFunctionName), $1 }
;

init_expression:
  expression                            { SINGLE_INIT (fst $1), snd $1 }
| LBRACE initializer_list_opt RBRACE    { let loc = makeLoc (startPos $1) (endPos $3) in
                                          COMPOUND_INIT (fst $2), loc }

initializer_list:    /* ISO 6.7.8. Allow a trailing COMMA */
  initializer                           { [fst $1], snd $1 }
| initializer COMMA initializer_list_opt
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }
;

initializer_list_opt:
  /* empty */                           { [], currentLoc () }
| initializer_list                      { $1 }
;

initializer: 
  init_designators eq_opt init_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1, fst $3), loc }
| gcc_init_designators init_expression
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1, fst $2), loc }
| init_expression                       { (NEXT_INIT, fst $1), snd $1 }
;

eq_opt: 
  EQ                                    { (), $1 }
  /*(* GCC allows missing = *)*/
| /*(* empty *)*/                       { (), currentLoc () }
;

init_designators: 
  DOT id_or_typename init_designators_opt
                                        { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          INFIELD_INIT(fst $2, fst $3), loc }
| LBRACKET  expression RBRACKET init_designators_opt
                                        { let loc = makeLoc (startPos $1) (endPos (snd $4)) in
                                          ATINDEX_INIT(fst $2, fst $4), loc }
| LBRACKET  expression ELLIPSIS expression RBRACKET
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          ATINDEXRANGE_INIT(fst $2, fst $4), loc }
;

init_designators_opt:
  /* empty */                           { NEXT_INIT, currentLoc () }
| init_designators                      { $1 }
;

gcc_init_designators:  /*(* GCC supports these strange things *)*/
  id_or_typename COLON                  { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          INFIELD_INIT(fst $1, NEXT_INIT), loc }
;

arguments: 
  /* empty */                           { [], currentLoc () }
| comma_expression                      { $1 }
;

opt_expression:
  /* empty */                           { NOTHING, currentLoc () }
| comma_expression                      { let es, loc = $1 in
                                          smooth_expression es loc, loc }
;

comma_expression:
  expression                            { [fst $1], snd $1 }
| expression COMMA comma_expression     { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          fst $1 :: fst $3, loc }
| error COMMA comma_expression          { let loc = makeLoc (startPos $2) (endPos (snd $3)) in
                                          (fst $3), loc }
;

comma_expression_opt:
  /* empty */                           { NOTHING, currentLoc () }
| comma_expression                      { let es, loc = $1 in
                                          smooth_expression es loc, loc }
;

paren_comma_expression:
  LPAREN comma_expression RPAREN        { let loc = makeLoc (startPos $1) (endPos $3) in
                                          (fst $2, loc) }
| LPAREN error RPAREN                   { let loc = makeLoc (startPos $1) (endPos $3) in
                                          [], loc }
;

bracket_comma_expression:
  LBRACKET comma_expression RBRACKET    { let loc = makeLoc (startPos $1) (endPos $3) in
                                          (fst $2, loc) }
| LBRACKET error RBRACKET               { let loc = makeLoc (startPos $1) (endPos $3) in
                                          ([], loc) }
;

/*** statements ***/
block: /* ISO 6.8.2 */
  block_begin local_labels block_attrs block_element_list RBRACE
                                        { !Lexerhack.pop_context();
                                          let loc = makeLoc (startPos $1) (endPos $5) in
                                          ({blabels = fst $2;
                                            battrs = fst $3;
                                            bstmts = fst $4;
                                            bloc = loc}, loc) }
| position error position RBRACE        { let loc = makeLoc $1 (endPos $4) in
                                          ({blabels = [];
                                            battrs  = [];
                                            bstmts  = [];
                                            bloc = loc}, loc) }
;

block_begin:
  LBRACE                                { !Lexerhack.push_context (); $1 }
;

block_attrs:
  /* empty */                           { [], currentLoc () }
| BLOCKATTRIBUTE paren_attr_list_ne     { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          [("__blockattribute__", fst $2)], loc }
;

/* statements and declarations in a block, in any order (for C99 support) */
block_element_list:
  /* empty */                           { [], currentLoc () }
| declaration block_element_list        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          DEFINITION (fst $1) :: (fst $2), loc }
| statement block_element_list          { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
/*(* GCC accepts a label at the end of a block *)*/
| IDENT COLON                           { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          [ LABEL (fst $1, NOP cabslu, loc)], loc }
| pragma block_element_list             { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          fst $2, loc }
;

local_labels:
  /* empty */                           { [], currentLoc () }
| LABEL__ local_label_names SEMICOLON local_labels 
                                        { let loc = makeLoc (startPos $1) (endPos (snd $4)) in
                                          (fst $2) @ (fst $4), loc }
;

local_label_names: 
  IDENT                                 { [ fst $1 ], snd $1 }
| IDENT COMMA local_label_names         { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }
;

statement:
  SEMICOLON                             { NOP $1, $1}
| comma_expression SEMICOLON            { let es, l1 = $1 in
                                          let loc = makeLoc (startPos l1) (endPos $2) in
                                          (COMPUTATION (smooth_expression es l1, loc), loc) }
| block                                 { (BLOCK (fst $1, snd $1), snd $1) }
| IF paren_comma_expression statement                    %prec IF
                                        { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          let es, l2 = $2 in
                                          (IF (smooth_expression es l2, fst $3, NOP cabslu, loc), loc) }
| IF paren_comma_expression statement ELSE statement
                                        { let loc = makeLoc (startPos $1) (endPos (snd $5)) in
                                          (IF (smooth_expression (fst $2) (snd $2), fst $3, fst $5, loc), loc) }
| SWITCH paren_comma_expression statement
                                        { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          (SWITCH (smooth_expression (fst $2) (snd $2), fst $3, loc), loc) }
| WHILE paren_comma_expression opt_hip_function_spec statement
                                        { let loc = makeLoc (startPos $1) (endPos (snd $4)) in
                                          (WHILE (smooth_expression (fst $2) (snd $2), fst $4, (fst $3), loc), loc) }
| DO opt_hip_function_spec statement WHILE paren_comma_expression SEMICOLON
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          (DOWHILE (smooth_expression (fst $5) (snd $5), fst $3, (fst $2), loc), loc) }
| FOR LPAREN for_clause opt_expression SEMICOLON opt_expression RPAREN opt_hip_function_spec statement
                                        { let loc = makeLoc (startPos $1) (endPos (snd $9)) in
                                          (FOR (fst $3, fst $4, fst $6, fst $9, (fst $8), loc), loc) }
| IDENT COLON attribute_nocv_list statement
                                        { (* The only attribute that should appear here
                                          is "unused". For now, we drop this on the
                                          floor, since unused labels are usually
                                          removed anyways by Rmtmps. *)
                                          let loc = makeLoc (startPos (snd $1)) (endPos (snd $4)) in
                                          (LABEL (fst $1, (fst $4), loc), loc)}
| CASE expression COLON statement       { let loc = makeLoc (startPos $1) (endPos (snd $4)) in
                                          (CASE (fst $2, fst $4, loc), loc) }
| CASE expression ELLIPSIS expression COLON statement
                                        { let loc = makeLoc (startPos $1) (endPos (snd $6)) in
                                          (CASERANGE (fst $2, fst $4, fst $6, loc), loc) }
| DEFAULT COLON statement               { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          (DEFAULT (fst $3, loc), loc) }
| RETURN SEMICOLON                      { let loc = makeLoc (startPos $1) (endPos $2) in
                                          (RETURN (NOTHING, loc), loc) }
| RETURN comma_expression SEMICOLON     { let loc = makeLoc (startPos $1) (endPos $3) in
                                          (RETURN (smooth_expression (fst $2) (snd $2), loc), loc) }
| BREAK SEMICOLON                       { let loc = makeLoc (startPos $1) (endPos $2) in
                                          (BREAK loc, loc) }
| CONTINUE SEMICOLON                    { let loc = makeLoc (startPos $1) (endPos $2) in
                                          (CONTINUE loc, loc) }
| GOTO IDENT SEMICOLON                  { let loc = makeLoc (startPos $1) (endPos $3) in
                                          (GOTO (fst $2, loc), loc) }
| GOTO STAR comma_expression SEMICOLON  { let loc = makeLoc (startPos $1) (endPos $4) in
                                          (COMPGOTO (smooth_expression (fst $3) (snd $3), loc), loc) }
| ASM asmattr LPAREN asmtemplate asmoutputs RPAREN SEMICOLON
                                        { let loc = makeLoc (startPos $1) (endPos $7) in
                                          (ASM (fst $2, fst $4, fst $5, loc), loc) }
| MSASM                                 { (ASM ([], [fst $1], None, (snd $1)), snd $1) }
| TRY block EXCEPT paren_comma_expression block
                                        { let loc = makeLoc (startPos $1) (endPos (snd $5)) in
                                          let b, _ = $2 in
                                          let h, _ = $5 in
                                          if not !Cprint.msvcMode then 
                                            parse_error "try/except in GCC code";
                                          (TRY_EXCEPT (b, COMMA (fst $4, snd $4), h, loc), loc) }
| TRY block FINALLY block               { let loc = makeLoc (startPos $1) (endPos (snd $4)) in
                                          let b, _ = $2 in
                                          let h, _ = $4 in
                                          if not !Cprint.msvcMode then 
                                            parse_error "try/finally in GCC code";
                                          (TRY_FINALLY (b, h, loc), loc) }
| position error position SEMICOLON     { let loc = makeLoc $1 (endPos $4) in
                                          (NOP loc, loc) }
| HIPSPEC                               { let hspec, loc = $1 in
                                          (HIP_STMT_SPEC (hspec, loc), loc) }
;

for_clause: 
  opt_expression SEMICOLON              { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          FC_EXP (fst $1), loc }
| declaration                           { FC_DECL (fst $1), snd $1 }
;

declaration:                                /* ISO 6.7.*/
  decl_spec_list init_declarator_list SEMICOLON
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $3) in
                                          (doDeclaration loc (fst $1) (fst $2), loc) }
| decl_spec_list SEMICOLON
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          (doDeclaration loc (fst $1) [], loc) }
;
init_declarator_list:                       /* ISO 6.7 */
  init_declarator                       { [fst $1], snd $1 }
| init_declarator COMMA init_declarator_list
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }

;
init_declarator:                             /* ISO 6.7 */
  declarator                            { (fst $1, NO_INIT), snd $1 }
| declarator EQ init_expression         { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1, fst $3), loc }
;

decl_spec_list:                         /* ISO 6.7 */
                                        /* ISO 6.7.1 */
| TYPEDEF decl_spec_list_opt            { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          SpecTypedef :: (fst $2), loc }
| EXTERN decl_spec_list_opt             { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          SpecStorage EXTERN :: (fst $2), loc }
| STATIC  decl_spec_list_opt            { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          SpecStorage STATIC :: (fst $2), loc }
| AUTO   decl_spec_list_opt             { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          SpecStorage AUTO :: (fst $2), loc }
| REGISTER decl_spec_list_opt           { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          SpecStorage REGISTER :: (fst $2), loc }
                                        /* ISO 6.7.2 */
| type_spec decl_spec_list_opt_no_named { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          SpecType (fst $1) :: (fst $2), loc }
                                        /* ISO 6.7.4 */
| INLINE decl_spec_list_opt             { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          SpecInline :: (fst $2), loc }
| cvspec decl_spec_list_opt             { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
| attribute_nocv decl_spec_list_opt     { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          SpecAttr (fst $1) :: (fst $2), loc }
/* specifier pattern variable (must be last in spec list) */
| AT_SPECIFIER LPAREN IDENT RPAREN      { let loc = makeLoc (startPos $1) (endPos $4) in
                                          [ SpecPattern(fst $3) ], loc }
;

/* (* In most cases if we see a NAMED_TYPE we must shift it. Thus we declare 
    * NAMED_TYPE to have right associativity  *) */
decl_spec_list_opt: 
  /* empty */                           { [], currentLoc () } %prec NAMED_TYPE
| decl_spec_list                        { $1 }
;

/* (* We add this separate rule to handle the special case when an appearance 
    * of NAMED_TYPE should not be considered as part of the specifiers but as 
    * part of the declarator. IDENT has higher precedence than NAMED_TYPE  *)
 */
decl_spec_list_opt_no_named: 
  /* empty */                           { [], currentLoc () } %prec IDENT
| decl_spec_list                        { $1 }
;

type_spec:   /* ISO 6.7.2 */
  VOID                                  { Tvoid, $1}
| CHAR                                  { Tchar, $1 }
| BOOL                                  { Tbool, $1 }
| SHORT                                 { Tshort, $1 }
| INT                                   { Tint, $1 }
| LONG                                  { Tlong, $1 }
| INT64                                 { Tint64, $1 }
| FLOAT                                 { Tfloat, $1 }
| DOUBLE                                { Tdouble, $1 }
| SIGNED                                { Tsigned, $1 }
| UNSIGNED                              { Tunsigned, $1 }
| STRUCT id_or_typename                 { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          Tstruct (fst $2, None, []), loc }
| STRUCT just_attributes id_or_typename { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          Tstruct (fst $3, None, fst $2), loc }
| STRUCT id_or_typename LBRACE struct_decl_list RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          Tstruct (fst $2, Some (fst $4), []), loc }
| STRUCT LBRACE struct_decl_list RBRACE { let loc = makeLoc (startPos $1) (endPos $4) in
                                          Tstruct ("", Some (fst $3), []), loc }
| STRUCT just_attributes id_or_typename LBRACE struct_decl_list RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          Tstruct (fst $3, Some (fst $5), fst $2), loc }
| STRUCT just_attributes LBRACE struct_decl_list RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          Tstruct ("", Some (fst $4), fst $2), loc }
| UNION id_or_typename                  { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          Tunion (fst $2, None, []), loc }
| UNION id_or_typename LBRACE struct_decl_list RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          Tunion  (fst $2, Some (fst $4), []), loc }
| UNION LBRACE struct_decl_list RBRACE  { let loc = makeLoc (startPos $1) (endPos $4) in
                                          Tunion ("", Some (fst $3), []), loc }
| UNION  just_attributes id_or_typename LBRACE struct_decl_list RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          Tunion (fst $3, Some (fst $5), fst $2), loc }
| UNION  just_attributes LBRACE struct_decl_list RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          Tunion ("", Some (fst $4), fst $2), loc }
| ENUM id_or_typename                   { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          Tenum (fst $2, None, []), loc }
| ENUM id_or_typename LBRACE enum_list maybecomma RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          Tenum (fst $2, Some (fst $4), []), loc }
| ENUM LBRACE enum_list maybecomma RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $5) in
                                          Tenum ("", Some (fst $3), []), loc }
| ENUM just_attributes id_or_typename LBRACE enum_list maybecomma RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $7) in
                                          Tenum (fst $3, Some (fst $5), fst $2), loc }
| ENUM just_attributes LBRACE enum_list maybecomma RBRACE
                                        { let loc = makeLoc (startPos $1) (endPos $6) in
                                          Tenum ("", Some (fst $4), fst $2), loc }
| NAMED_TYPE                            { Tnamed (fst $1), snd $1 }
| TYPEOF LPAREN expression RPAREN       { let loc = makeLoc (startPos $1) (endPos $4) in
                                          TtypeofE (fst $3), loc }
| TYPEOF LPAREN type_name RPAREN        { let loc = makeLoc (startPos $1) (endPos $4) in
                                          let s, d, _ = $3 in
                                          TtypeofT (s, d), loc }
;

struct_decl_list: /* (* ISO 6.7.2. Except that we allow empty structs. We 
                      * also allow missing field names. *)
                   */
 /* empty */                            { [], currentLoc () }
| decl_spec_list SEMICOLON struct_decl_list
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1, [(missingFieldDecl, None)]) :: (fst $3), loc }
/*(* GCC allows extra semicolons *)*/
| SEMICOLON struct_decl_list            { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          fst $2, loc }
| decl_spec_list field_decl_list SEMICOLON struct_decl_list
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $4)) in
                                          (fst $1, fst $2) :: (fst $4), loc }
/*(* MSVC allows pragmas in strange places *)*/
| pragma struct_decl_list               { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          fst $2, loc }
| error SEMICOLON struct_decl_list      { let loc = makeLoc (startPos $2) (endPos (snd $3)) in
                                          fst $3, loc }
;

field_decl_list: /* (* ISO 6.7.2 *) */
  field_decl                            { [fst $1], snd $1 }
| field_decl COMMA field_decl_list      { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }
;

field_decl: /* (* ISO 6.7.2. Except that we allow unnamed fields. *) */
| declarator                            { (fst $1, None), snd $1 }
| declarator COLON expression attributes
                                        { let (n,decl,al,l) = fst $1 in
                                          let al' = al @ (fst $4) in
                                          let loc = makeLoc (startPos (snd $1)) (endPos (snd $4)) in
                                          ((n,decl,al',l), Some (fst $3)), loc }
| COLON expression                      { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          (missingFieldDecl, Some (fst $2)), loc }
;

enum_list: /* (* ISO 6.7.2.2 *) */
  enumerator                            { [fst $1], snd $1 }
| enum_list COMMA enumerator            { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) @ [fst $3], loc }
| enum_list COMMA error                 { let loc = makeLoc (startPos (snd $1)) (endPos $2) in
                                          fst $1, loc } 
;

enumerator:  
  IDENT                                 { (fst $1, NOTHING, snd $1), snd $1 }
| IDENT EQ expression                   { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1, fst $3, loc), loc }
;

declarator:  /* (* ISO 6.7.5. Plus Microsoft declarators.*) */
  pointer_opt direct_decl attributes_with_asm
                                        { let (n, decl) = fst3 $2, snd3 $2 in
                                          let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (n, applyPointer (fst $1) decl, fst $3, loc), loc }
;

direct_decl: /* (* ISO 6.7.5 *) */
                                   /* (* We want to be able to redefine named
                                    * types as variable names *) */
| id_or_typename                        { (fst $1, JUSTBASE, snd $1) }
| LPAREN attributes declarator RPAREN   { let (n,decl,al, _) = fst $3 in
                                          let loc = makeLoc (startPos $1) (endPos $4) in
                                          (n, PARENTYPE((fst $2),decl,al), loc) }
| direct_decl LBRACKET attributes comma_expression_opt RBRACKET
                                        { let (n, decl, l1) = $1 in
                                          let loc = makeLoc (startPos l1) (endPos $5) in
                                          (n, ARRAY(decl, fst $3, fst $4), loc) }
| direct_decl LBRACKET attributes error RBRACKET
                                        { let (n, decl, l1) = $1 in
                                          let loc = makeLoc (startPos l1) (endPos $5) in
                                          (n, ARRAY(decl, fst $3, NOTHING), loc) }
| direct_decl parameter_list_startscope rest_par_list RPAREN
                                        { let (n, decl, l1) = $1 in
                                          let (params, isva) = $3 in
                                          !Lexerhack.pop_context ();
                                          let loc = makeLoc (startPos l1) (endPos $4) in
                                          (n, PROTO(decl, params, isva), loc) }
;

parameter_list_startscope: 
  LPAREN                                { !Lexerhack.push_context () }
;

rest_par_list:
| /* empty */                           { ([], false) }
| parameter_decl rest_par_list1         { let (params, isva) = $2 in 
                                          ((fst $1) :: params, isva) }
;

rest_par_list1: 
  /* empty */                           { ([], false) }
| COMMA ELLIPSIS                        { ([], true) }
| COMMA parameter_decl rest_par_list1   { let (params, isva) = $3 in 
                                          ((fst $2) :: params, isva) }
;

parameter_decl: /* (* ISO 6.7.5 *) */
  decl_spec_list declarator             { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1, fst $2), loc }
| decl_spec_list abstract_decl          { let d, a, l2 = $2 in
                                          let loc = makeLoc (startPos (snd $1)) (endPos l2) in
                                          (fst $1, ("", d, a, l2)), loc }
| decl_spec_list                        { (fst $1, ("", JUSTBASE, [], cabslu)), snd $1 }
| LPAREN parameter_decl RPAREN          { let loc = makeLoc (startPos $1) (endPos $3) in
                                          (fst $2), loc } 
;

/* (* Old style prototypes. Like a declarator *) */
old_proto_decl:
  pointer_opt direct_old_proto_decl     { let (n, decl, a, l2) = $2 in
                                          let loc = makeLoc (startPos (snd $1)) (endPos l2) in
                                          (n, applyPointer (fst $1) decl, a, loc), loc }
;

direct_old_proto_decl:
  direct_decl LPAREN old_parameter_list_ne RPAREN old_pardef_list
                                        { let par_decl, isva = doOldParDecl (fst $3) (fst $5) in
                                          let n, decl, l1 = $1 in
                                          let loc = makeLoc (startPos l1) (endPos (snd $5)) in
                                          (n, PROTO(decl, par_decl, isva), [], loc) }
| direct_decl LPAREN RPAREN             { let n, decl, l1 = $1 in
                                          let loc = makeLoc (startPos l1) (endPos $3) in
                                          (n, PROTO(decl, [], false), [], loc) }
/* (* appears sometimesm but generates a shift-reduce conflict. *)
| LPAREN STAR direct_decl LPAREN old_parameter_list_ne RPAREN RPAREN LPAREN RPAREN old_pardef_list
                                   { let par_decl, isva 
                                             = doOldParDecl $5 $10 in
                                     let n, decl = $3 in
                                     (n, PROTO(decl, par_decl, isva), [])
                                   }
*/
;

old_parameter_list_ne:
| IDENT                                 { [fst $1], snd $1 }
| IDENT COMMA old_parameter_list_ne     { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          let rest = fst $3 in
                                          (fst $1 :: rest), loc }
;

old_pardef_list: 
  /* empty */                           { ([], false), currentLoc () }
| decl_spec_list old_pardef SEMICOLON ELLIPSIS
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          ([(fst $1, fst $2)], true), loc }
| decl_spec_list old_pardef SEMICOLON old_pardef_list
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $4)) in
                                          let rest, isva = fst $4 in
                                          ((fst $1, fst $2) :: rest, isva), loc }
;

old_pardef: 
  declarator                            { [fst $1], snd $1 }
| declarator COMMA old_pardef           { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }
| error                                 { [], currentLoc () }
;

pointer: /* (* ISO 6.7.5 *) */ 
  STAR attributes pointer_opt           { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          (fst $2) :: (fst $3), loc }
;

pointer_opt:
  /**/                                  { [], currentLoc () }
| pointer                               { $1 }
;

type_name: /* (* ISO 6.7.6 *) */
  decl_spec_list abstract_decl          { let d, a, l2 = $2 in
                                          if a <> [] then begin
                                            parse_error "attributes in type name";
                                            raise Parsing.Parse_error
                                          end;
                                          let loc = makeLoc (startPos (snd $1)) (endPos l2) in
                                          (fst $1, d, loc) }
| decl_spec_list                        { (fst $1, JUSTBASE, snd $1) }
;

abstract_decl: /* (* ISO 6.7.6. *) */
  pointer_opt abs_direct_decl attributes
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (applyPointer (fst $1) (fst $2), fst $3, loc) }
| pointer                               { (applyPointer (fst $1) JUSTBASE, [], snd $1) }
;

abs_direct_decl: /* (* ISO 6.7.6. We do not support optional declarator for 
                     * functions. Plus Microsoft attributes. See the 
                     * discussion for declarator. *) */
| LPAREN attributes abstract_decl RPAREN
                                        { let d, a, _ = $3 in
                                          let loc = makeLoc (startPos $1) (endPos $4) in
                                          PARENTYPE (fst $2, d, a), loc }
            
| LPAREN error RPAREN                   { let loc = makeLoc (startPos $1) (endPos $3) in
                                          JUSTBASE, loc } 
            
| abs_direct_decl_opt LBRACKET comma_expression_opt RBRACKET
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          ARRAY(fst $1, [], fst $3), loc }
/*(* The next should be abs_direct_decl_opt but we get conflicts *)*/
| abs_direct_decl parameter_list_startscope rest_par_list RPAREN
                                        { let (params, isva) = $3 in
                                          !Lexerhack.pop_context ();
                                          let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          PROTO (fst $1, params, isva), loc } 
;

abs_direct_decl_opt:
  abs_direct_decl                       { $1 }
| /* empty */                           { JUSTBASE, currentLoc () }
;

function_def:  /* (* ISO 6.9.1 *) */
  function_def_start opt_hip_function_spec block  
                                        { let (specs, decl, l1) = $1 in
                                          let loc = makeLoc (startPos l1) (endPos (snd $3)) in
                                          currentFunctionName := "<__FUNCTION__ used outside any functions>";
                                          !Lexerhack.pop_context (); (* The context pushed by announceFunctionName *)
                                          (doFunctionDef loc specs decl (fst $2) (fst $3), loc) }
| function_def_start opt_hip_function_spec SEMICOLON
                                        { let (specs, decl, l1) = $1 in
                                          let loc = makeLoc (startPos l1) (endPos $3) in
                                          currentFunctionName := "<__FUNCTION__ used outside any functions>";
                                          !Lexerhack.pop_context (); (* The context pushed by announceFunctionName *)
                                          let emptyblock = {blabels = [];
                                                            battrs  = [];
                                                            bstmts  = [];
                                                            bloc = $3} in
                                          (doFunctionDef loc specs decl (fst $2) emptyblock, loc) }
;

function_def_start:  /* (* ISO 6.9.1 *) */
   decl_spec_list declarator            { announceFunctionName (fst $2);
                                          let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1, fst $2, loc) }
/* (* Old-style function prototype *) */
| decl_spec_list old_proto_decl         { announceFunctionName (fst $2);
                                          let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1, fst $2, loc) }
/* (* New-style function that does not have a return type *) */
| IDENT parameter_list_startscope rest_par_list RPAREN 
                                        { let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          let (params, isva) = $3 in
                                          let fdec = (fst $1, PROTO(JUSTBASE, params, isva), [], loc) in
                                          announceFunctionName fdec;
                                          (* Default is int type *)
                                          let defSpec = [SpecType Tint] in
                                          (defSpec, fdec, loc) }
/* (* No return type and old-style parameter list *) */
| IDENT LPAREN old_parameter_list_ne RPAREN old_pardef_list
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $5)) in
                                          (* Convert pardecl to new style *)
                                          let pardecl, isva = doOldParDecl (fst $3) (fst $5) in
                                          (* Make the function declarator *)
                                          let fdec = (fst $1, PROTO(JUSTBASE, pardecl,isva), [], loc) in
                                          announceFunctionName fdec;
                                          (* Default is int type *)
                                          let defSpec = [SpecType Tint] in
                                          (defSpec, fdec, loc) }
/* (* No return type and no parameters *) */
| IDENT LPAREN RPAREN                   { let loc = makeLoc (startPos (snd $1)) (endPos $3) in
                                          (* Make the function declarator *)
                                          let fdec = (fst $1, PROTO(JUSTBASE, [], false), [], loc) in
                                          announceFunctionName fdec;
                                          (* Default is int type *)
                                          let defSpec = [SpecType Tint] in
                                          (defSpec, fdec, loc) }
;

/* const/volatile as type specifier elements */
cvspec:
  CONST                                 { SpecCV(CV_CONST), $1 }
| VOLATILE                              { SpecCV(CV_VOLATILE), $1 }
| RESTRICT                              { SpecCV(CV_RESTRICT), $1 }
;

/*** GCC attributes ***/
attributes:
  /* empty */                           { [], currentLoc () }
| attribute attributes                  { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
;

/* (* In some contexts we can have an inline assembly to specify the name to 
    * be used for a global. We treat this as a name attribute *) */
attributes_with_asm:
  /* empty */                           { [], currentLoc () }
| attribute attributes_with_asm         { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
| ASM LPAREN string_constant RPAREN attributes
                                        { let loc = makeLoc (startPos $1) (endPos (snd $5)) in
                                          ("__asm__", [CONSTANT(CONST_STRING (fst $3), snd $3)]) :: (fst $5), loc }
;

/* things like __attribute__, but no const/volatile */
attribute_nocv:
  ATTRIBUTE LPAREN paren_attr_list RPAREN
                                        { let loc = makeLoc (startPos $1) (endPos $4) in
                                          ("__attribute__", fst $3), loc }
/*(*
| ATTRIBUTE_USED                      { ("__attribute__", 
                                             [ VARIABLE "used" ]), $1 }
*)*/
| DECLSPEC paren_attr_list_ne           { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          ("__declspec", fst $2), loc }
| MSATTR                                { (fst $1, []), snd $1 }
                                        /* ISO 6.7.3 */
| THREAD                                { ("__thread",[]), $1 }
| QUALIFIER                             { ("__attribute__",[VARIABLE(fst $1, snd $1)]),snd $1 }
;

attribute_nocv_list:
  /* empty */                           { [] }
| attribute_nocv attribute_nocv_list    { fst $1 :: $2 }
;

/* __attribute__ plus const/volatile */
attribute:
  attribute_nocv                        { $1 }
| CONST                                 { ("const", []), $1 }
| RESTRICT                              { ("restrict",[]), $1 }
| VOLATILE                              { ("volatile",[]), $1 }
;

/* (* sm: I need something that just includes __attribute__ and nothing more,
 *  to support them appearing between the 'struct' keyword and the type name. 
 * Actually, a declspec can appear there as well (on MSVC) *)  */
just_attribute:
  ATTRIBUTE LPAREN paren_attr_list RPAREN
                                        { let loc = makeLoc (startPos $1) (endPos $4) in
                                          ("__attribute__", fst $3), loc }
| DECLSPEC paren_attr_list_ne           { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          ("__declspec", fst $2), loc }
;

/* this can't be empty, b/c I folded that possibility into the calling
 * productions to avoid some S/R conflicts */
just_attributes:
  just_attribute                        { [fst $1], snd $1 }
| just_attribute just_attributes        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
;

/** (* PRAGMAS and ATTRIBUTES *) ***/
pragma: 
| PRAGMA attr PRAGMA_EOL                { let loc = makeLoc (startPos $1) (endPos $3) in
                                          (PRAGMA (fst $2, loc), loc) }
| PRAGMA attr SEMICOLON PRAGMA_EOL      { let loc = makeLoc (startPos $1) (endPos  $4) in
                                          (PRAGMA (fst $2, loc), loc) }
| PRAGMA_LINE                           { (PRAGMA (VARIABLE (fst $1, snd $1), snd $1), snd $1) }
;

/* (* We want to allow certain strange things that occur in pragmas, so we 
    * cannot use directly the language of expressions *) */ 
primary_attr: 
  IDENT                                 { VARIABLE (fst $1, snd $1), snd $1 }
  /*(* The NAMED_TYPE here creates conflicts with IDENT *)*/
| NAMED_TYPE                            { VARIABLE (fst $1, snd $1), snd $1 } 
| LPAREN attr RPAREN                    { let loc = makeLoc (startPos $1) (endPos $3) in
                                          fst $2, loc } 
| IDENT IDENT                           { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          CALL(VARIABLE (fst $1, snd $1), [VARIABLE (fst $2, snd $2)], loc), loc }
| CST_INT                               { CONSTANT(CONST_INT (fst $1), snd $1), snd $1 }
| string_constant                       { CONSTANT(CONST_STRING (fst $1), snd $1), snd $1 }
                                           /*(* Const when it appears in 
                                            * attribute lists, is translated 
                                            * to aconst *)*/
| CONST                                 { VARIABLE ("aconst", $1), $1 }
| IDENT COLON CST_INT                   { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          VARIABLE ((fst $1) ^ ":" ^ (fst $3), loc), loc }
/*(* The following rule conflicts with the ? : attributes. We give it a very 
   * low priority *)*/
| CST_INT COLON CST_INT                 { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          VARIABLE ((fst $1) ^ ":" ^ (fst $3), loc), loc } 
| DEFAULT COLON CST_INT                 { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          VARIABLE ("default:" ^ (fst $3), loc), loc }
                                            /*(** GCC allows this as an 
                                             * attribute for functions, 
                                             * synonim for noreturn **)*/
| VOLATILE                              { VARIABLE ("__noreturn__", $1), $1 }
;

postfix_attr:
  primary_attr                          { $1 }
                                         /* (* use a VARIABLE "" so that the 
                                             * parentheses are printed *) */
| IDENT LPAREN RPAREN                   { let loc = makeLoc (startPos (snd $1)) (endPos $3) in
                                          let l1 = makeLoc (startPos $2) (endPos $3) in
                                          CALL(VARIABLE (fst $1, snd $1), [VARIABLE ("", l1)], loc), loc }
| IDENT paren_attr_list_ne              { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          CALL(VARIABLE (fst $1, snd $1), fst $2, loc), loc }
| postfix_attr ARROW id_or_typename     { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          MEMBEROFPTR (fst $1, fst $3, loc), loc } 
| postfix_attr DOT id_or_typename       { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          MEMBEROF (fst $1, fst $3, loc), loc }  
| postfix_attr LBRACKET attr RBRACKET   { let loc = makeLoc (startPos (snd $1)) (endPos $4) in
                                          INDEX (fst $1, fst $3, loc), loc }
;

/*(* Since in attributes we use both IDENT and NAMED_TYPE as indentifiers, 
 * that leads to conflicts for SIZEOF and ALIGNOF. In those cases we require 
 * that their arguments be expressions, not attributes *)*/
unary_attr:
  postfix_attr                          { $1 }
| SIZEOF unary_expression               { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          EXPR_SIZEOF (fst $2, loc), loc }
| SIZEOF LPAREN type_name RPAREN        { let b, d, _ = $3 in
                                          let loc = makeLoc (startPos $1) (endPos $4) in
                                          TYPE_SIZEOF (b, d, loc), loc }
| ALIGNOF unary_expression              { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          EXPR_ALIGNOF (fst $2, loc), loc }
| ALIGNOF LPAREN type_name RPAREN       { let b, d, _ = $3 in
                                          let loc = makeLoc (startPos $1) (endPos $4) in
                                          TYPE_ALIGNOF (b, d, loc), loc }
| PLUS cast_attr                        { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (PLUS, fst $2, loc), loc }
| MINUS cast_attr                       { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (MINUS, fst $2, loc), loc }
| STAR cast_attr                        { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (MEMOF, fst $2, loc), loc }
| AND cast_attr                         { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (ADDROF, fst $2, loc), loc }
| EXCLAM cast_attr                      { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (NOT, fst $2, loc), loc }
| TILDE cast_attr                       { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          UNARY (BNOT, fst $2, loc), loc }
;

cast_attr:
  unary_attr                            { $1 }
;

multiplicative_attr:
  cast_attr                             { $1 }
| multiplicative_attr STAR cast_attr    { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(MUL, fst $1 , fst $3, loc), loc }
| multiplicative_attr SLASH cast_attr   { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(DIV, fst $1 , fst $3, loc), loc }
| multiplicative_attr PERCENT cast_attr { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(MOD, fst $1 , fst $3, loc), loc }
;


additive_attr:
  multiplicative_attr                   { $1 }
| additive_attr PLUS multiplicative_attr
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(ADD, fst $1 , fst $3, loc), loc } 
| additive_attr MINUS multiplicative_attr
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SUB, fst $1 , fst $3, loc), loc }
;

shift_attr:
  additive_attr                         { $1 }
| shift_attr INF_INF additive_attr      { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SHL, fst $1 , fst $3, loc), loc }
| shift_attr SUP_SUP additive_attr      { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(SHR, fst $1 , fst $3, loc), loc }
;

relational_attr:
  shift_attr                            { $1 }
| relational_attr INF shift_attr        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(LT, fst $1 , fst $3, loc), loc }
| relational_attr SUP shift_attr        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(GT, fst $1 , fst $3, loc), loc }
| relational_attr INF_EQ shift_attr     { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(LE, fst $1 , fst $3, loc), loc }
| relational_attr SUP_EQ shift_attr     { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(GE, fst $1 , fst $3, loc), loc }
;

equality_attr:
  relational_attr                       { $1 }
| equality_attr EQ_EQ relational_attr   { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(EQ, fst $1 , fst $3, loc), loc }
| equality_attr EXCLAM_EQ relational_attr
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(NE, fst $1 , fst $3, loc), loc }
;


bitwise_and_attr:
  equality_attr                         { $1 }
| bitwise_and_attr AND equality_attr    { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(BAND, fst $1 , fst $3, loc), loc }
;

bitwise_xor_attr:
  bitwise_and_attr                      { $1 }
| bitwise_xor_attr CIRC bitwise_and_attr
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(XOR, fst $1, fst $3, loc), loc }
;

bitwise_or_attr: 
  bitwise_xor_attr                      { $1 }
| bitwise_or_attr PIPE bitwise_xor_attr { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(BOR, fst $1, fst $3, loc), loc }
;

logical_and_attr:
  bitwise_or_attr                       { $1 }
| logical_and_attr AND_AND bitwise_or_attr
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(AND, fst $1, fst $3, loc), loc }
;

logical_or_attr:
  logical_and_attr                      { $1 }
| logical_or_attr PIPE_PIPE logical_and_attr
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          BINARY(OR,fst $1 , fst $3, loc), loc }
;

conditional_attr: 
  logical_or_attr                       { $1 }
/* This is in conflict for now */
| logical_or_attr QUEST conditional_attr COLON conditional_attr 
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $5)) in
                                          QUESTION(fst $1, fst $3, fst $5, loc), loc }


attr:
  conditional_attr                      { $1 }
;

attr_list_ne:
| attr                                  { [fst $1], snd $1 }
| attr COMMA attr_list_ne               { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }
| error COMMA attr_list_ne              { let loc = makeLoc (startPos $2) (endPos (snd $3)) in
                                          fst $3, loc }
;

attr_list:
  /* empty */                           { [], currentLoc () }
| attr_list_ne                          { $1 }
;

paren_attr_list_ne: 
  LPAREN attr_list_ne RPAREN            { let loc = makeLoc (startPos $1) (endPos $3) in
                                          fst $2, loc }
| LPAREN error RPAREN                   { let loc = makeLoc (startPos $1) (endPos $3) in
                                          [], loc }
;

paren_attr_list: 
  LPAREN attr_list RPAREN               { let loc = makeLoc (startPos $1) (endPos $3) in
                                          fst $2, loc }
| LPAREN error RPAREN                   { let loc = makeLoc (startPos $1) (endPos $3) in
                                          [], loc }
;

/*** GCC ASM instructions ***/
asmattr:
  /* empty */                           { [], currentLoc () }
| VOLATILE asmattr                      { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          ("volatile", []) :: (fst $2), loc }
| CONST asmattr                         { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          ("const", []) :: (fst $2), loc } 
;

asmtemplate: 
  one_string_constant                   { [fst $1], snd $1 }
| one_string_constant asmtemplate       { let loc = makeLoc (startPos (snd $1)) (endPos (snd $2)) in
                                          (fst $1) :: (fst $2), loc }
;

asmoutputs: 
  /* empty */                           { None, currentLoc () }
| COLON asmoperands asminputs           { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          let (ins, clobs) = fst $3 in
                                          Some {aoutputs = fst $2; ainputs = ins; aclobbers = clobs}, loc }
;

asmoperands:
  /* empty */                           { [], currentLoc () }
| asmoperandsne                         { List.rev (fst $1), snd $1 }
;

asmoperandsne:
  asmoperand                            { [fst $1], snd $1 }
| asmoperandsne COMMA asmoperand        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $3) :: (fst $1), loc }
;

asmoperand:
  asmopname string_constant LPAREN expression RPAREN    { let loc = makeLoc (startPos (snd $1)) (endPos $5) in
                                                          (fst $1, fst $2, fst $4), loc }
| asmopname string_constant LPAREN error RPAREN         { let loc = makeLoc (startPos (snd $1)) (endPos $5) in
                                                          (fst $1, fst $2, NOTHING), loc } 
;

asminputs: 
  /* empty */                           { ([], []), currentLoc () }
| COLON asmoperands asmclobber          { let loc = makeLoc (startPos $1) (endPos (snd $3)) in
                                          (fst $2, fst $3), loc }
;

asmopname:
  /* empty */                           { None, currentLoc () }
| LBRACKET IDENT RBRACKET               { let loc = makeLoc (startPos $1) (endPos $3) in
                                          Some (fst $2), loc }
;

asmclobber:
  /* empty */                           { [], currentLoc () }
| COLON asmcloberlst_ne                 { let loc = makeLoc (startPos $1) (endPos (snd $2)) in
                                          fst $2, loc }
;

asmcloberlst_ne:
  one_string_constant                   { [fst $1], snd $1 }
| one_string_constant COMMA asmcloberlst_ne
                                        { let loc = makeLoc (startPos (snd $1)) (endPos (snd $3)) in
                                          (fst $1) :: (fst $3), loc }
;

/** hip functions' specification */
opt_hip_function_spec:
  /* empty */                           { None , currentLoc ()}
| HIPSPEC                               { let spec, loc = $1 in
                                          Some (spec, loc), loc }


%%



