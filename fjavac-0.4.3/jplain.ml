(* jplain.ml - java plain (untyped) abstract syntax tree *)


module L = Listx
module S = Jsyntax

open Std


(*

Still valid java program.

0. Restructuring AST.

- variable arguments (Vararg) becomes an optional 'formal'
- insert default constructor if missing

1. Syntactic sugar (not recovered):

- vdecl is expanded and eliminated: 'Field', 'ForDecl' and 'Vdecl'. In
particular, ForDecl is translated into a block containing the
declarations (JLS 14.14.1.1). This normalization simplies the type of
variable declaration: in the original sytax, the type can appear after
the varible. This normalization also simplies the binding, as each
declaration now introduce exactly one variable.

Optional initialization becomes no initialization, followed by an
optional assignment expression.

- Field initializations are moved to class initialization block.

- array bounds are specified with the type instead of the variables
(formal, signat)

- Variable declarations and initializations are hoisted outside the
loops to simplify the definitions of ForEach, ForDecl and ForExp. They
are enclosed by a Block to ensure that the lexical scopes of variables
remain the same. A tricky point is that labels preceding the loop
statement must be collected and inserted after the initialization
expressions, otherwise 'continue l' will re-evaluate and re-initialize
the values by jumping to the beginning of the translated code.

- for-decl loop:

l1: .. ln: for (d; e2; es) s
  ==  { d; l1: .. ln: for (; e2; es) s

- for-each loop:
l1: .. ln: for (t x : e) s  
  ==  { I i; i = e.iterator(); l1: .. ln: for (; i.hasNext();) { t x = i.next(); s }}   fresh i

l1: .. ln: for (t x : e) s  
  ==  { t[] a = e; int i; i = 0; l1: .. ln: for (; i < a.length; i++) { t x = a[i]; s }}  fresh a,i



2. Interchangeable syntactic sugar (recovered during printing):

- extend: class x {...}  ==  class x extends Object {...}
- if: if (e) s  ==  if (e) s {}
- preincrement: ++e  ==  e += 1
- predecrement: --e  ==  e -= 1
- postincrement: e++ == e =+ 1
- postdecrement: e-- == e =- 1
- conditional-or: e1 || e2  ==  e1 ? true : e2
- conditional-and: e1 && e2  ==  e1 ? e2 : false
- annotation marker: @n  ==  @n()
- annotation single: @n(e)  ==  @n(value=e)
- for-loop test: for (es1; ; es2) s  ==  for (es1; true; es2) s



3. Slight extension of the langauge:

- class Object extends Object { ... }
- post assignments: x =+ 3


*)

type ctask = cunit list                 (* compilation task *)
and cunit = name * import list * decl list (* compilation unit *)
and block = stmt list                   (* statement block *)
and exps = exp list                     (* expression list *)
and tys = ty list                       (* type list *)
and expo = exp option                   (* expression option *)
and catch = modifiers * ty * id * block (* exception catch clause *)
and enumconst = modifiers * id * exps * body list (* enumeration constant *)
and formal = modifiers * ty * id        (* formal argument *)
and import = info * bool * name * bool  (* import declaration: static? and all? *)
and modifiers = modifier list           (* type modifier list *)
and name = string list                  (* qualified name *)
and tparams = (id * ty * tys) list       (* type parameters *)
and id = string                         (* identifier *)
and info = string                       (* line info *)


(* method signature: formal arguments, variable arity argument, annotation default, 
array dimension, exception names *)
and signat = formal list * formal option * expo * name list 

and decl =                              (* type declaration *)
  | Class of info * modifiers * id * tparams * ty * tys * body list
  | Iface of info * modifiers * id * tparams * tys * body list
  | Enum of info * modifiers * id * tys * enumconst list * body list
  | Annot of info * modifiers * id * body list

and ty =                                (* type *)
  | Tarray of ty * int           (* array: base type and dimension *)
  | Tinst of ty * wty list       (* instantiated / generic C<T..T> *)
  | Tname of name                (* partially-qualified name *)
  | Tbool
  | Tbyte
  | Tchar
  | Tdouble
  | Tfloat
  | Tint
  | Tlong
  | Tshort
  | Tvoid

and wty =                              (* wild card type *)
  | WildType of ty                 (* non-wildcard type *)
  | WildCard                    (* ? *)
  | WildExtends of ty            (* ? extends T *)
  | WildSuper of ty              (* ? super T *)

and body =                              (* declaration body *)
  | Init of info * bool * block            (* initialization *)
  | Inner of info * decl                   (* inner declaration *)
  | Ctor of info * modifiers * tparams * id * signat * block
  | Method of info * modifiers * tparams * ty * id * signat * block option
  | Field of info * modifiers * ty * id

and stmt =                              (* statement *)
  | Assert of info * exp * expo
  | Block of info * block
  | Break of info * id option
  | Case of info * exp
  | Continue of info * id option
  | Default of info
  | Do of info * stmt * exp
  | Exp of info * exp
  | ForEach of info * block * id * exp * stmt (* block of label statements *)
  | ForExp of info * exp * exps * stmt
  | If of info * exp * stmt * stmt
  | Label of info * id
  | Local of info * decl
  | Return of info * expo
  | Switch of info * exp * block
  | Sync of info * exp * block
  | Throw of info * exp
  | Try of info * block * catch list * block
  | Vdecl of info * modifiers * ty * id
  | While of info * exp * stmt

and exp =                               (* expression *)
  | Escape of info * exp                   (* INTERNAL *)
  | Array of info * exps                   (* array initializer *)
  | Assign of info * bool * exp * assign * exp (* assigment *)
  | Binary of info * exp * binary * exp    (* binary operation *)
  | Instof of info * exp * ty             (* instance-of test *)
  | Cond of info * exp * exp * exp         (* conditional *)
  | Cast of info * ty * exp               (* type cast *)
  | Pos of info * exp                      (* positive *)
  | Neg of info * exp                      (* negative *)
  | Not of info * exp                      (* negation *)
  | Inv of info * exp                      (* inversion *)
  | Offset of info * exp * exp             (* offset *)
  | Dot of info * exp * exp             (* select *)
  | ExpClass of info * ty                  (* class type *)
  | Invoke of info * exp * exps         (* method invoke *)
  | Inst of info * wty list * exp       (* instantiation *)
  | True of info                           (* true *)
  | False of info                          (* false *)
  | Null of info                           (* null *)
  | This of info                           (* this *)
  | Super of info                          (* super *)
  | Char of info * string                  (* character *)
  | Int of info * int32                 (* integer *)
  | Long of info * int64                (* long integer *)
  | Float of info * float               (* single-precision floating point *)
  | Double of info * float              (* double-precision floating point *)
  | Str of info * string                   (* string *)
  | Ident of info * id                      (* identifier *)
  | NewArrNone of info * ty * exp list * int (* array creation *)
  | NewArrSome of info * ty * exps (* array creation *)
  | NewObj of info * name * wty list * exps * body list (* object creation *)

and binary =                            (* binary operator *)
  | Or                                  (* or *)
  | Xor                                 (* xor *)
  | And                                 (* and *)
  | Eq                                  (* equal *)
  | Ne                                  (* unequal *)
  | Lt                                  (* less-than *)
  | Gt                                  (* greater-than *)
  | Le                                  (* less-than-equal *)
  | Ge                                  (* greater-than-equal *)
  | Shl                                 (* left shift *)
  | Shr                                 (* right shift *)
  | Ushr                                (* unsigned right shift *)
  | Add                                 (* add *)
  | Sub                                 (* subtract *)
  | Mul                                 (* multiply *)
  | Div                                 (* divide *)
  | Rem                                 (* modulus *)

and assign =                            (* assignment operator *)
  | Set 
  | AddSet 
  | SubSet 
  | MulSet 
  | DivSet 
  | RemSet 
  | AndSet 
  | OrSet 
  | XorSet 
  | ShlSet 
  | ShrSet 
  | UshrSet 

and modifier =                          (* type modifier *)
  | Annotate of info * name * (id * exp) list
  | Abstract 
  | Final 
  | Native 
  | Private 
  | Protected 
  | Public 
  | Static 
  | Strictfp 
  | Synchronized 
  | Transient 
  | Volatile 


(*---- Eqaulity *)

let x_eq (x1:id) (x2:id) : bool = (x1 = x2)
let name_eq (n1:name) (n2:name) : bool = L.all2 x_eq n1 n2

let rec ty_eq (t1:ty) (t2:ty) : bool =
  t1 = t2 ||
  match (t1,t2) with
  | (Tarray (t3,n1),Tarray (t4,n2)) -> ty_eq t3 t4 && n1=n2
  | (Tinst (t3,w1),Tinst (t4,w2)) -> 
    ty_eq t3 t4 && L.all2 wty_eq w1 w2
  | (Tname (n1),Tname (n2)) -> name_eq n1 n2
  | (Tbool,Tbool) -> true
  | (Tbyte,Tbyte) -> true
  | (Tchar,Tchar) -> true
  | (Tfloat,Tfloat) -> true
  | (Tdouble,Tdouble) -> true
  | (Tint,Tint) -> true
  | (Tlong,Tlong) -> true
  | (Tshort,Tshort) -> true
  | (Tvoid,Tvoid) -> true
  | _ -> false

and wty_eq (w1:wty) (w2:wty) : bool =
  match (w1,w2) with
  | (WildType (t1), WildType (t2)) -> ty_eq t1 t2
  | (WildCard, WildCard) -> true
  | (WildExtends (t1), WildExtends (t2)) -> ty_eq t1 t2
  | (WildSuper (t1), WildSuper (t2)) -> ty_eq t1 t2
  | _ -> false

let rec is_object : ty -> bool = function
  | Tname n -> name_is_object n
  | _ -> false

and name_is_object (n:name) : bool = 
  name_eq n ["Object"] || name_eq n ["java";"lang";"Object"]


(*---- Show as source code. *)

(* java.lang.Boolean$C$D$E -> (["java";"lang";"Boolean";"C";"D";"E"]) *)
let name_read (x:string) : name = 
  match Strx.read '$' x with
  | [] -> assert_false () (* INVARIANT: Strx.read *)
  | [y] -> Strx.read '.' y
  | y::ys -> Strx.read '.' y @ ys


(* FIXME: put parenthesis according to precendence and associativity *)
(* TODO: identation (by piping to 'indent-region' of java mode in  emacs?) *)
(* TODO: break long lines? OCaml Format module? *)

let rec ctask_show (t:ctask) : string = 
  L.show "\n---- %s\n" cunit_show t

and cunit_show ((no,is,ds):cunit) : string = 
  showf "%s%s%s\n" (package_show no)
  (if is=[] then "" else L.show1 import_show is ^ "\n\n") 
  (L.show2 decl_show ds)

and package_show n = 
  if n=[] then "" else showf "package %s;\n\n" (name_show n)

and import_show (_,s,x1,x2) = 
  showf "import %s%s%s;" (if_show "static " s)
  (name_show x1) (if_show ".*" x2)

and name_show x0 = showf "%s" (L.show "." x_show x0)

and x_show x : string = x

and decl_show = function
  | Class (_,x0,x1,x2,x3,x4,x5) -> 
    showf "%sclass %s%s%s%s %s" (modifiers_show x0)
   (x_show x1) (tparams_show x2) (extend_show x3) 
   (implements_show x4) (bodies_show x5)
  | Iface (_,x0,x1,x2,x3,x4) ->
    showf "%sinterface %s %s %s %s" (modifiers_show x0) 
    (x_show x1) (tparams_show x2) (extends_show x3) (bodies_show x4)
  | Enum (_,x0,x1,x2,x3,x4) ->
    showf "%senum %s %s { %s %s }" (modifiers_show x0)
    (x_show x1) (implements_show x2) (L.showz enumconst_show x3) (bodies_show x4)
  | Annot (_,x0,x1,x2) -> 
    showf "%s@@interface %s %s" (modifiers_show x0) (x_show x1) (bodies_show x2)

and tparams_show x0 = 
  if x0=[] then "" else showf "<%s>" (L.show "," tparam_show x0 ^ " ")

and tparam_show (x0,x1,x2) = 
  showf "%s %s %s" (x_show x0) (extend_show x1) (L.show "," tinter_show x2)

and tinter_show x0 = showf "& %s" (ty_show x0)

and targs_show x0 = if x0=[] then "" else showf "<%s>" (L.show "," wty_show x0)

and wty_show = function
  | WildType x0 -> showf "%s" (ty_show x0)
  | WildCard -> showf "?" 
  | WildExtends x0 -> showf "? extends %s" (ty_show x0)
  | WildSuper x0 -> showf "? super %s" (ty_show x0)

and extend_show t = if is_object t then "" else showf " extends %s" (ty_show t)

and extends_show x0 = showf " extends %s" (L.show "," ty_show x0)

and implements_show x0 = showf " implements %s" (L.show ", " ty_show x0)

and ty_show = function
  | Tarray (x0,x1) -> showf "%s%s" (ty_show x0) (dimen_show x1)
  | Tinst (x0,x1) -> showf "%s%s" (ty_show x0) (targs_show x1)
  | Tname (x0) -> showf "%s" (name_show x0)
  | Tbool -> showf "boolean" 
  | Tbyte -> showf "byte" 
  | Tchar -> showf "char" 
  | Tdouble -> showf "double" 
  | Tfloat -> showf "float" 
  | Tint -> showf "int" 
  | Tlong -> showf "long" 
  | Tshort -> showf "short" 
  | Tvoid -> showf "void" 

and dimen_show i = Strx.repeat i "[]" 

and body_show = function
  | Init (_,x0,x1) ->
    showf "%s %s" (if_show "static" x0) (block_show x1)
  | Inner (_,x0) ->
    showf "%s" (decl_show x0)
  | Ctor (_,x0,x1,x2,x3,x4) ->
    showf "%s%s%s%s %s" (modifiers_show x0) (tparams_show x1) (x_show x2) 
    (signat_show x3) (block_show x4)
  | Method (_,x0,x1,x2,x3,x4,None) ->
    showf "%s%s%s %s%s;" (modifiers_show x0) (tparams_show x1) (ty_show x2) 
    (x_show x3) (signat_show x4)
  | Method (_,x0,x1,x2,x3,x4,Some x5) ->
    showf "%s%s%s %s%s %s" (modifiers_show x0) (tparams_show x1) (ty_show x2) 
    (x_show x3) (signat_show x4) (block_show x5)
  | Field (_,x0,x1,x2) ->
    showf "%s%s %s;" (modifiers_show x0) (ty_show x1) (x_show x2)

and enumconst_show (ms,x0,x1,x2) 
  = showf "%s%s %s %s" (modifiers_show ms) (x_show x0) (arg_show x1) (bodies_show x2)

and bodies_show x0 = 
  if x0=[] then "{\n}" else showf "{\n%s\n}" (L.show2 body_show x0)

and signat_show (x0,x,x1,x3) = 
  showf " (%s%s)%s%s" (L.show ", " formal_show x0) (opt_show vararg_show x)
  (opt_show default_show x1) (throws_show x3)

and default_show x0 = showf "default %s" (exp_show x0)

and arg_show (x0:exps) = showf "(%s)" (L.show ", " exp_show x0)

and modifiers_show x = if x=[] then "" else L.showz modifier_show x ^ " "

and stmt_show = function
  | ForEach (_,ls,x2,x3,x4) ->
    showf "%sfor (%s : %s) %s" (L.showz stmt_show ls)
    (x_show x2) (exp_show x3) (stmt_show x4)
  | ForExp (_,True _,x2,x3) ->
    showf "for (;; %s) %s" (L.show ", " exp_show x2) (stmt_show x3)
  | ForExp (_,x1,x2,x3) ->
    showf "for (; %s; %s) %s" (exp_show x1)
    (L.show "," exp_show x2) (stmt_show x3)
  | While (_,x0,x1) ->
    showf "while (%s) %s" (exp_show x0) (stmt_show x1)
  | If (_,x0,x1,Block (_,[])) ->
    showf "if (%s) %s" (exp_show x0) (stmt_show x1) 
  | If (_,x0,x1,x2) ->
    showf "if (%s) %s else %s" (exp_show x0) (stmt_show x1) (stmt_show x2)
  | Assert (_,x0,None) ->
    showf "assert %s;" (exp_show x0)
  | Assert (_,x0,Some x1) ->
    showf "assert %s: %s;" (exp_show x0) (exp_show x1)
  | Block (_,x0) ->
    showf "%s" (block_show x0)
  | Break (_,x0) ->
    showf "break%s;" (opt_space_show x_show x0)
  | Case (_,x0) ->
    showf "case %s:" (exp_show x0)
  | Continue (_,x0) ->
    showf "continue%s;" (opt_space_show x_show x0)
  | Vdecl (_,x0,x1,x2) ->
    showf "%s%s %s;" (modifiers_show x0) (ty_show x1) (x_show x2)
  | Default (_) ->
    showf "default:" 
  | Do (_,x0,x1) ->
    showf "do %s while (%s);" (stmt_show x0) (exp_show x1)
  | Exp (_,x0) ->
    showf "%s;" (exp_show x0)
  | Label (_,x0) ->
    showf "%s:" (x_show x0)
  | Local (_,x0) ->
    showf "%s" (decl_show x0)
  | Return (_,x0) ->
    showf "return%s;" (opt_space_show exp_show x0)
  | Switch (_,x0,x1) ->
    showf "switch (%s) %s" (exp_show x0) (block_show x1)
  | Sync (_,x0,x1) ->
    showf "synchronized (%s) %s" (exp_show x0) (block_show x1)
  | Throw (_,x0) ->
    showf "throw %s;" (exp_show x0)
  | Try (_,x0,x1,x2) ->
    showf "try %s %s%s" (block_show x0) (L.show1 catch_show x1) (finally_show x2)

and block_show (x0:block) : string = 
  if x0=[] then "{\n}" else showf "{\n%s\n}" (L.show1 stmt_show x0)

and catch_show (ms,x,x0,x1) = 
  showf "catch (%s%s %s) %s" (modifiers_show ms) 
  (ty_show x) (x_show x0) (block_show x1)

and finally_show x0 = 
  if x0=[] then "" else showf " finally %s" (block_show x0)

and throws_show x0 = 
  if x0=[] then "" else showf " throws %s" (L.show ", " name_show x0)

and formal_show (x0,x1,x2) = 
  showf "%s%s %s" (modifiers_show x0) (ty_show x1) (x_show x2) 

and vararg_show (x0,x1,x2) = 
  showf ", %s%s... %s" (modifiers_show x0) (ty_show x1) (x_show x2)

(* FIXME FIXME: parenthesize *)
and exp_show : exp -> string = function
  | Escape (_,e) -> "\\" ^ exp_show e
  | Array (_,x0) ->
    showf "{ %s }" (L.show ", " exp_show x0)
  | Assign (_,true,e0,AddSet,Int(_,1l)) -> showf "++%s" (exp_show e0)
  | Assign (_,true,e0,SubSet,Int(_,1l)) -> showf "--%s" (exp_show e0)
  | Assign (_,false,e0,AddSet,Int(_,1l)) -> showf "++%s" (exp_show e0)
  | Assign (_,false,e0,SubSet,Int(_,1l)) -> showf "--%s" (exp_show e0)
  | Assign (_,true,x0,x1,x2) ->
    showf "%s %s %s" (exp_show x0) (assign_show x1) (exp_show x2)
  | Assign (_,false,x0,x1,x2) -> error "Invalid proper Java code"
  | Cond (_,e1,True _,e2) -> showf "%s || %s" (exp_show e1) (exp_show e2)
  | Cond (_,e1,e2,False _) -> showf "%s && %s" (exp_show e1) (exp_show e2)
  | Cond (_,x0,x1,x2) ->
    showf "%s ? %s : %s" (exp_show x0) (exp_show x1) (exp_show x2)
  | Binary (_,x1,x2,x3) ->
    showf "%s %s %s" (exp_show x1) (binary_show x2) (exp_show x3)
  | Instof (_,x0,x1) ->
    showf "%s instanceof %s" (exp_show x0) (ty_show x1)
  | Cast (_,x0,x1) ->
    showf "(%s)%s" (ty_show x0) (exp_show x1)
  | Pos (_,x0) ->
    showf "+%s" (exp_show x0)
  | Neg (_,x0) ->
    showf "-%s" (exp_show x0)
  | Not (_,x0) ->
    showf "!%s" (exp_show x0)
  | Inv (_,x0) ->
    showf "~%s" (exp_show x0)
  | Offset (_,x0,x1) ->
    showf "%s[%s]" (exp_show x0) (exp_show x1)
  | Dot (_,x0,x1) ->
    showf "%s.%s" (exp_show x0) (exp_show x1)
  | ExpClass (_,x0) ->
    showf "%s.class" (ty_show x0)
  | Invoke (_,x0,x1) ->
    showf "%s%s" (exp_show x0) (arg_show x1)
  | Inst (_,ts,e) -> (targs_show ts) ^ (exp_show e)
  | True _ ->
    showf "true" 
  | False _ ->
    showf "false" 
  | Null _ ->
    showf "null" 
  | This _ ->
    showf "this" 
  | Super _ ->
    showf "super" 
  | Char (_,x0) -> "'" ^ x0 ^ "'"
  | Long (_,x0) -> int64_show x0 ^ "l"
  | Int (_,x0) -> int32_show x0
  | Float (_,x0) -> float_show x0 ^ "f"
  | Double (_,x0) -> float_show x0 ^ "d"
  | Str (_,x) -> Strx.code x
  | Ident (_,x0) -> 
    showf "%s" (x_show x0)
  | NewArrNone (_,t,es,i) ->
    showf "new %s%s %s" (ty_show t) (L.show0 size_show es) (dimen_show i)
  | NewArrSome (_,t,es) ->
    showf "new %s { %s }" (ty_show t) (L.show "," exp_show es)
  | NewObj (_,x0,x1,x2,x3) ->
    showf "new %s%s%s%s" (name_show x0) (targs_show x1) (arg_show x2) 
    (opt_list_show bodies_show x3)

and size_show e = showf "[%s]" (exp_show e)

and assign_show = function
  | Set -> "=" 
  | AddSet -> "+=" 
  | SubSet -> "-=" 
  | MulSet -> "*=" 
  | DivSet -> "/=" 
  | RemSet -> "%%=" 
  | AndSet -> "&=" 
  | OrSet -> "|=" 
  | XorSet -> "^=" 
  | ShlSet -> "<<=" 
  | ShrSet -> ">> =" 
  | UshrSet -> ">>> =" 

and binary_show = function
  | Or -> "|"
  | Xor -> "^"
  | And -> "&"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | Shl -> "<<"
  | Shr -> ">>"
  | Ushr -> ">>>"
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Rem -> "%"

and modifier_show = function
  | Annotate (_,x0,[]) -> showf "@@%s" (name_show x0)
  | Annotate (_,x0,[("value",e)]) -> 
    showf "@@%s(%s)" (name_show x0) (exp_show e)
  | Annotate (_,x0,x1) ->
    showf "@@%s(%s)" (name_show x0) (L.show "," labelexp_show x1)
  | Abstract -> "abstract" 
  | Final -> "final" 
  | Native -> "native" 
  | Private -> "private" 
  | Protected -> "protected" 
  | Public -> "public" 
  | Static -> "static" 
  | Strictfp -> "strictfp" 
  | Synchronized -> "synchronized" 
  | Transient -> "transient" 
  | Volatile -> "volatile" 

and labelexp_show (x0,x1) = showf "%s = %s" (x_show x0) (exp_show x1)


(*-- Translate Gsyntax into here... *)

(* push array dimension into the type *)
let array_type (t:ty) (n:int) = 
  match (t,n) with
  | (_,0) -> t
  | (Tarray (t2,n2),_) -> Tarray (t2,n+n2)
  | _ -> Tarray (t,n)

let rec ctask_of (t:S.cunit list) : ctask = L.map cunit_of t

and cunit_of ((p,x1,x2):S.cunit) : cunit = 
  (package_of p, L.map import_of x1, L.collect decl_of x2)

and package_of = function
  | None -> []
  | Some (_,n) -> name_of n

and import_of (z,is_static,name,is_all) : import = 
  (z,is_static, name_of name, is_some is_all)

and exps_of es = L.map exp_of es
and name_of n = n
and id_of x = x

and decl_of : S.decl -> decl option = function
  | S.Class (z,x0,x1,x2,x3,x4,x5) -> 
    Some (Class (z, modifiers_of x0, id_of x1, tparams_of x2, 
    ty_opt_map x3, types_of x4, bodies_of z x0 x1 x5))
  | S.Iface (z,x0,x1,x2,x3,x4) -> 
    Some (Iface (z, modifiers_of x0, id_of x1, 
    tparams_of x2, types_of x3, bodies_of z x0 x1 x4))
    (* FIXME: need default constructor for enum? *)
  | S.Enum (z,x0,x1,x2, S.EnumNone (x3,_,_)) -> 
    Some (Enum (z, modifiers_of x0, id_of x1, types_of x2, 
    L.map enumconst_of x3, []))
  | S.Enum (z,x0,x1,x2, S.EnumSome (x3,_,x4)) -> 
    Some (Enum (z, modifiers_of x0, id_of x1, types_of x2, 
    L.map enumconst_of x3, bodies_of z x0 x1 x4))
  | S.Annot (z,x0,x1,x2) -> (* FIXME: need default constructor for annot? *)
    Some (Annot (z, modifiers_of x0, id_of x1, bodies_of z x0 x1 x2))
  | S.Empty _ -> None

and tparams_of : S.tparams option -> tparams = function
  | None -> []
  | Some ts -> L.map tparam_of ts

and tparam_of (x0,x1,x2) : id * ty * tys = 
  (id_of x0, ty_opt_map x1, L.map ty_z_of x2)

and ty_opt_map = function
  | None -> Tname ["Object"]
  | Some t -> ty_of t

and ty_z_of t : ty = ty_of t

and targs_of = function
  | None -> []
  | Some ts -> L.map wty_of ts

and wty_of = function
  | S.WildType x0 -> WildType (ty_of x0)
  | S.WildCard -> WildCard
  | S.WildExtends x0 -> WildExtends (ty_of x0)
  | S.WildSuper x0 -> WildSuper (ty_of x0)

and types_of = function
  | None -> []
  | Some ts -> L.map ty_of ts

and ty_of = function
  | S.Tarray (x0,x1) -> Tarray (ty_of x0, L.size x1)
  | S.Tinst (x0,x1) -> Tinst (ty_of x0, L.map wty_of x1)
  | S.Tname (x0) -> Tname (name_of x0)
  | S.Tbool -> Tbool
  | S.Tbyte -> Tbyte
  | S.Tchar -> Tchar
  | S.Tdouble -> Tdouble
  | S.Tfloat -> Tfloat
  | S.Tint -> Tint
  | S.Tlong -> Tlong
  | S.Tshort -> Tshort
  | S.Tvoid -> Tvoid

and modifiers_of (ms:S.modifier list) = L.map modifier_of ms

and body_of : S.body -> body list = function
  | S.Init (z,x0,x1) -> 
    [Init (z, x0, block_of x1)]
  | S.Inner (z,x0) -> 
    (match decl_of x0 with Some b -> [Inner (z, b)] | _ -> [])
  | S.Ctor (z,x0,x1,x2,x3,x4) -> 
    [Ctor (z, modifiers_of x0, tparams_of x1, id_of x2, 
    signat_of x3, block_of x4)]
  | S.MethodNone (z,x0,x1,x2,x3,x4) -> 
    let (_,_,x,_) = x4 in           (* additional array bound *)
    let t2 = array_type (ty_of x2) (L.size x) in (* push array type into return type *)
    [Method (z, modifiers_of x0, tparams_of x1, 
    t2, id_of x3, signat_of x4, None)]
  | S.MethodSome (z,x0,x1,x2,x3,x4,x5) -> 
    [Method (z, modifiers_of x0, tparams_of x1, 
    ty_of x2, id_of x3, signat_of x4, Some (block_of x5))]
  | S.Field (z,x0,x1,vs) -> 
    L.mapc (fun (((s as x),d,vo):S.vdecl) ->
      let t = array_type (ty_of x1) (L.size d) in
      let f = function
        | None -> []
        | Some e -> 
          (* initialization: x = e *)
          let e2 = Assign (z, true, Ident (z, id_of x), Set, exp_of e) in
          [Init (z, false, [Exp (z, e2)])] in
      Field (z, modifiers_of x0, t, id_of x) :: f vo) vs

and enumconst_of (ms,x0,x1,x2) = (modifiers_of ms, id_of x0, arg_of x1, bodies_option_of x2)

and bodies_option_of = function
  | None -> []
  | Some bs -> L.mapc body_of bs

and default_of (x0:S.adefault) : exp = exp_of x0

and signat_of ((x0,x1,n,x3):S.signat) : signat = 
  let (y1,y2) = formals_of x0 in
  (y1, y2, opt_map default_of x1, throws_of x3)

and arg_of = function
  | None -> []
  | Some es -> exps_of es

and stmt_of (ls:block) : S.stmt -> stmt list  = function
  | S.ForDecl (z,x0,x1,x2,x3,x4,x5) ->  (* JLS 14.14.1.1 *)
    let ss1 = stmt_of [] (S.Vdecl (z, x0, x1, x2)) in
    let ss2 = stmt_of ls (S.ForExp (z, [], x3, x4, x5)) in
    [Block (z, ss1 @ ss2)]
  | S.ForEach (z,x0,x1,x2,x3,x4) -> 
    let s1 = Vdecl (z, modifiers_of x0, ty_of x1, id_of x2) in
    let s2 = ForEach (z, ls, id_of x2, exp_of x3, stmts_of x4) in
    [Block (z, [s1; s2])]
  | S.ForExp (z,x0,x1,x2,x3) -> 
    let test = match x1 with None -> True z | Some e -> exp_of e in
    let init = L.map (fun e -> Exp (z, exp_of e)) x0 in
    init @ ls @ [ForExp (z, test, exps_of x2, stmts_of x3)]
  | S.While (z,x0,x1) -> ls @ [While (z, exp_of x0, stmts_of x1)]
  | S.If (z,x0,x1,None) -> ls @ [If (z, exp_of x0, stmts_of x1, Block (z,[]))]
  | S.If (z,x0,x1,Some x2) -> ls @ [If (z, exp_of x0, stmts_of x1, stmts_of x2)]
  | S.AssertNone (z,x0) -> ls @ [Assert (z, exp_of x0, None)]
  | S.AssertSome (z,x0,x1) -> ls @ [Assert (z, exp_of x0, Some (exp_of x1))]
  | S.Block (z,x0) -> ls @ [Block (z, block_of x0)]
  | S.Break (z,x0) -> ls @ [Break (z, opt_map id_of x0)]
  | S.Case (z,x0) -> ls @ [Case (z, exp_of x0)]
  | S.Continue (z,x0) -> ls @ [Continue (z, opt_map id_of x0)]
  | S.Vdecl (z,x0,x1,vs) -> 
    ls @ L.mapc (fun ((x,d,vo):S.vdecl) ->
      let t = array_type (ty_of x1) (L.size d) in
      let f = function
        | None -> []
        | Some e -> [Exp (z, Assign (z, true, Ident (z, id_of x), Set, exp_of e))] in
      Vdecl (z, modifiers_of x0, t, id_of x) :: (f vo)) vs
  | S.Default z -> ls @ [Default (z)]
  | S.Do (z,x0,x1) -> ls @ [Do (z, stmts_of x0, exp_of x1)]
  | S.Exp (z,x0) -> ls @ [Exp (z, exp_of x0)]
  | S.Label (z,x0,s) -> stmt_of (Label (z, id_of x0) :: ls) s
  | S.Local (z,x0) -> 
    ls @ [match decl_of x0 with Some b -> Local (z, b) | _ -> Block (z,[])]
  | S.Return (z,x0) -> ls @ [Return (z, opt_map exp_of x0)]
  | S.Switch (z,x0,x1) -> ls @ [Switch (z, exp_of x0, block_of x1)]
  | S.Sync (z,x0,x1) -> ls @ [Sync (z, exp_of x0, block_of x1)]
  | S.Throw (z,x0) -> ls @ [Throw (z, exp_of x0)]
  | S.Try (z,x0,x1,x2) -> 
    ls @ [Try (z, block_of x0, L.map catch_of x1, finally_of x2)]

and stmts_of (s:S.stmt) : stmt =
  match stmt_of [] s with
  | [] -> assert_false ()                  (* stmt_of produces lists of size > 0 *)
  | [x] -> x
  | x -> Block ("",x)

and block_of ss = L.mapc (stmt_of []) ss  

and catch_of ((ms,x0,x,x1):S.catch) : catch = 
  (modifiers_of ms, ty_of x0, id_of x, block_of x1)

and finally_of = function
  | None -> []
  | Some b -> block_of b

and throws_of = function
  | None -> []
  | Some ns -> L.map name_of ns

and formals_of : S.formals -> formal list * formal option = function
  | S.ArgMore (x0,x1,x2,x3,x4) ->
    let y = formal_of (x0,x1,x2,x3) in
    let (y1,y2) = formals_of x4 in
    (y::y1, y2)
  | S.ArgFix (x0,x1,x2,x3) -> ([formal_of (x0,x1,x2,x3)], None)
  | S.ArgVar (x0,x1,x2,x3) -> ([], Some (formal_of (x0,x1,x2,x3)))
  | S.ArgNone -> ([], None)

and formal_of (x0,x1,x2,x3) = 
  (* push dimension from trailing the variable name into the type *)
  let t2 = array_type (ty_of x1) (L.size x3) in
  (modifiers_of x0, t2, id_of x2)

and exp_of : S.exp -> exp = function
  | S.Escape (z,e) -> Escape (z, exp_of e)
  | S.Array (z,x0) -> Array (z, expsx_of x0)
  | S.Assign (z,x0,x1,x2) -> Assign (z, true, exp_of x0, assign_of x1, exp_of x2)
  | S.Cond (z,x0,x1,x2) -> Cond (z, exp_of x0, exp_of x1, exp_of x2)
  | S.Cor (z,x0,x1) -> Cond (z, exp_of x0, True z, exp_of x1)
  | S.Cand (z,x0,x1) -> Cond (z, exp_of x0, exp_of x1, False z)
  | S.Or (z,x0,x1) -> Binary (z, exp_of x0, Or, exp_of x1)
  | S.Xor (z,x0,x1) -> Binary (z, exp_of x0, Xor, exp_of x1)
  | S.And (z,x0,x1) -> Binary (z, exp_of x0, And, exp_of x1)
  | S.Eq (z,x0,x1) -> Binary (z, exp_of x0, Eq, exp_of x1)
  | S.Ne (z,x0,x1) -> Binary (z, exp_of x0, Ne, exp_of x1)
  | S.Lt (z,x0,x1) -> Binary (z, exp_of x0, Lt, exp_of x1)
  | S.Gt (z,x0,x1) -> Binary (z, exp_of x0, Gt, exp_of x1)
  | S.Le (z,x0,x1) -> Binary (z, exp_of x0, Le, exp_of x1)
  | S.Ge (z,x0,x1) -> Binary (z, exp_of x0, Ge, exp_of x1)
  | S.Shl (z,x0,x1) -> Binary (z, exp_of x0, Shl, exp_of x1)
  | S.Shr (z,x0,x1) -> Binary (z, exp_of x0, Shr, exp_of x1)
  | S.Ushr (z,x0,x1) -> Binary (z, exp_of x0, Ushr, exp_of x1)
  | S.Add (z,x0,x1) -> Binary (z, exp_of x0, Add, exp_of x1)
  | S.Sub (z,x0,x1) -> Binary (z, exp_of x0, Sub, exp_of x1)
  | S.Mul (z,x0,x1) -> Binary (z, exp_of x0, Mul, exp_of x1)
  | S.Div (z,x0,x1) -> Binary (z, exp_of x0, Div, exp_of x1)
  | S.Rem (z,x0,x1) -> Binary (z, exp_of x0, Rem, exp_of x1)
  | S.Instof (z,x0,x1) -> Instof (z, exp_of x0, ty_of x1)
  | S.Cast (z,x0,x1) -> Cast (z, ty_of x0, exp_of x1)
  | S.PreIncr (z,x0) -> Assign (z, true, exp_of x0, AddSet, Int (z,1l))
  | S.PreDecr (z,x0) -> Assign (z, true, exp_of x0, SubSet, Int (z,1l))
  | S.PostIncr (z,x0) -> Assign (z, false, exp_of x0, AddSet, Int (z,1l))
  | S.PostDecr (z,x0) -> Assign (z, false, exp_of x0, SubSet, Int (z,1l))
  | S.Pos (z,x0) -> Pos (z, exp_of x0)
  | S.Neg (z,x0) -> Neg (z, exp_of x0)
  | S.Not (z,x0) -> Not (z, exp_of x0)
  | S.Inv (z,x0) -> Inv (z, exp_of x0)
  | S.Offset (z,x0,x1) -> Offset (z, exp_of x0, exp_of x1)
  | S.Dot (z,x0,x1) -> Dot (z, exp_of x0, exp_of x1)
  | S.ExpClass (z,x0) -> ExpClass (z, ty_of x0)
  | S.Invoke (z,x0,x1) -> Invoke (z, exp_of x0, exps_of x1)
  | S.Inst (z,ts,e) -> Inst (z, L.map wty_of ts, exp_of e)
  | S.True z -> True (z)
  | S.False z -> False (z)
  | S.Null z -> Null (z)
  | S.This z -> This (z)
  | S.Super z -> Super (z)
  | S.Char (z,x0) -> Char (z, x0)
  | S.Long (z,x0) -> Long (z, x0)
  | S.Int (z,x0) -> Int (z, x0)
  | S.Float (z,x0) -> Float (z, x0)
  | S.Double (z,x0) -> Double (z, x0)
  | S.Str (z,x0) -> Str (z, x0)
  | S.Ident (z,x0) -> Ident (z, id_of x0)
  | S.Atom (z,x0) -> exp_of x0
  | S.NewArrNone (z,x0,x2,x3) -> 
    NewArrNone (z, ty_of x0, L.map (fun e -> exp_of e) x2, L.size x3)
  | S.NewArrSome (z,x0,x3) -> NewArrSome (z, ty_of x0, expsx_of x3)
  | S.NewObj (z,x0,x1,x2,x3) -> 
    NewObj (z, name_of x0, targs_of x1, exps_of x2, bodies_option_of x3)

and bodies_of (z:info) (ms:S.modifier list) (x:id) (bs:S.bodies) : body list =
  let bs2 = L.mapc body_of bs in
  (* JVM 2.12 default constructors *)
  let n = L.count (function S.Ctor _ -> true | _ -> false) bs in
  let p = L.some (function S.Public _ -> true | _ -> false) ms in
  let m = if p then [Public] else [] in
  let s = ([], None, None, []) in
  let b = [Exp (z, Invoke (z, Super z, []))] in
  if n > 0 then bs2 else Ctor (z, m, [], x, s, b) :: bs2

and expsx_of = function
  | S.ExpsCons (e,s) -> exp_of e :: expsx_of s
  | S.ExpsSome e -> [exp_of e]
  | S.ExpsNil -> []

and assign_of = function
  | S.Set -> Set
  | S.AddSet -> AddSet
  | S.SubSet -> SubSet
  | S.MulSet -> MulSet
  | S.DivSet -> DivSet
  | S.RemSet -> RemSet
  | S.AndSet -> AndSet
  | S.OrSet -> OrSet
  | S.XorSet -> XorSet
  | S.ShlSet -> ShlSet
  | S.ShrSet -> ShrSet
  | S.UshrSet -> UshrSet

and modifier_of = function
  | S.AnnotMark (z,x0) -> 
    Annotate (z, name_of x0, [])
  | S.AnnotSingle (z,x0,x1) -> 
    Annotate (z, name_of x0, [("value",exp_of x1)])
  | S.AnnotMore (z,x0,x1) -> 
    Annotate (z, name_of x0, L.map labelexp_of x1)
  | S.Abstract z -> Abstract
  | S.Final z -> Final
  | S.Native z -> Native
  | S.Private z -> Private
  | S.Protected z -> Protected
  | S.Public z -> Public
  | S.Static z -> Static
  | S.Strictfp z -> Strictfp
  | S.Synchronized z -> Synchronized
  | S.Transient z -> Transient
  | S.Volatile z -> Volatile

and labelexp_of (x0,x1) = (id_of x0, exp_of x1)


(*---- file info *)

let rec decl_info = function                
  | Class (z,_,_,_,_,_,_) -> z
  | Iface (z,_,_,_,_,_) -> z
  | Enum (z,_,_,_,_,_) -> z
  | Annot (z,_,_,_) -> z

and body_info = function
  | Init (z,_,_) -> z
  | Inner (z,_) -> z
  | Ctor (z,_,_,_,_,_) -> z
  | Method (z,_,_,_,_,_,_) -> z
  | Field (z,_,_,_) -> z

let stmt_info = function
  | Assert (z,_,_) -> z
  | Block (z,_) -> z
  | Break (z,_) -> z
  | Case (z,_) -> z
  | Continue (z,_) -> z
  | Default z -> z
  | Do (z,_,_) -> z
  | Exp (z,_) -> z
  | ForEach (z,_,_,_,_) -> z
  | ForExp (z,_,_,_) -> z
  | If (z,_,_,_) -> z
  | Label (z,_) -> z
  | Local (z,_) -> z
  | Return (z,_) -> z
  | Switch (z,_,_) -> z
  | Sync (z,_,_) -> z
  | Throw (z,_) -> z
  | Try (z,_,_,_) -> z
  | Vdecl (z,_,_,_) -> z
  | While (z,_,_) -> z

and exp_info = function
  | Escape (z,_) -> z
  | Array (z,_) -> z
  | Assign (z,_,_,_,_) -> z
  | Binary (z,_,_,_) -> z
  | Instof (z,_,_) -> z
  | Cond (z,_,_,_) -> z
  | Cast (z,_,_) -> z
  | Pos (z,_) -> z
  | Neg (z,_) -> z
  | Not (z,_) -> z
  | Inv (z,_) -> z
  | Offset (z,_,_) -> z
  | Dot (z,_,_) -> z
  | ExpClass (z,_) -> z
  | Invoke (z,_,_) -> z
  | Inst (z,_,_) -> z
  | True z -> z
  | False z -> z
  | Null z -> z
  | This z -> z
  | Super z -> z
  | Char (z,_) -> z
  | Long (z,_) -> z
  | Int (z,_) -> z
  | Float (z,_) -> z
  | Double (z,_) -> z
  | Str (z,_) -> z
  | Ident (z,_) -> z
  | NewArrNone (z,_,_,_) -> z
  | NewArrSome (z,_,_) -> z
  | NewObj (z,_,_,_,_) -> z


(*---- Accessors. *)

let array_base : ty -> ty = function
  | Tarray (t,n) -> if n=1 then t else Tarray (t,n-1)
  | t -> error "not array type: %s" (ty_show t)

(* type membership *)
let ty_mem (t:ty) (ts:tys) : bool = L.some (ty_eq t) ts

let decl_x : decl -> id = function
  | Class (_,_,x,_,_,_,_) -> x
  | Iface (_,_,x,_,_,_) -> x
  | Enum (_,_,x,_,_,_) -> x
  | Annot (_,_,x,_) -> x

let decl_modifiers : decl -> modifiers = function
  | Class (_,ms,_,_,_,_,_) -> ms
  | Iface (_,ms,_,_,_,_) -> ms
  | Enum (_,ms,_,_,_,_) -> ms
  | Annot (_,ms,_,_) -> ms

let decl_is_class : decl -> bool = function
  | Class _ -> true | _ -> false

let decl_is_iface : decl -> bool = function
  | Iface _ -> true | _ -> false

let body_field_x : body -> id option = function
  | Field (_,_,_,x) -> Some x
  | _ -> None

let decl_bodies : decl -> body list = function
  | Class (_,_,_,_,_,_,bs) -> bs
  | Iface (_,_,_,_,_,bs) -> bs
  | Enum (_,_,_,_,_,bs) -> bs
  | Annot (_,_,_,bs) -> bs

let rec name_of_ty (z:info) : ty -> name = function
  | Tarray (t,_) -> name_of_ty z t
  | Tinst (t,_) -> name_of_ty z t
  | Tname n -> n
  | t -> error "%s: name_of_ty: %s is a primitive type" z (ty_show t)

let ty_is_name : ty -> bool = function
  | Tname _ -> true 
  | _ -> false

let rec ty_name : ty -> name = function
  | Tname n -> n
  | Tinst (t,_) -> ty_name t
  | t -> error "no class name for type %s" (ty_show t)

let decl_bounds : decl -> tys = function
  | Class (_,_,_,_,t,ts,_) -> t :: ts
  | Iface (_,_,_,_,ts,_) -> ts
  | Enum (_,_,_,ts,_,_) -> ts
  | Annot _ -> (* todo *) assert_false ()

let bounds_show (ts:tys) : string = 
  if ts=[] then "" else "<:" ^ L.show "&" ty_show ts

let xs_show (xs:id list) : string = L.show ", " x_show xs
let ts_show (ts:ty list) : string = L.show ", " ty_show ts
