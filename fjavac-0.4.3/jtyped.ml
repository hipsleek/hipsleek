(* jtyped.ml - java typed abstract syntax tree *)


module H = Hashx
module L = Listx
module M = Mapx
module P = Jplain
open Std                              


(* 

Design choice: most contextual information is encoded directly in the
datatype, including package, enclosing classes, types.

difference with jplain.ml:
 
1. expression annotated with types (extractable independent of subtyping 
   and context, ie. using 'exp_ty')
2. variable resolved to integer index 
3. explicit promotion, boxing (no subtyping)
4. overloading resolution: 
     explict method signature at invocation
     explicit field names at assignment and identifiers
     differentiate tname into tclass and tiface

- compound assignment expansion: left-hand side is evaluated only
once: 'store variable' can be expanded (x += y becomes x = x + y). but
'store array variable' cannot not be expanded because the computation
of array index may be duplicated; similarly, 'get field' cannot be
expanded because the computation of base object may be duplicated. immediate 

- break assignment into 1. field put, and 2. array store, 3. variable store

- pre-assignment vs. post-assignment

- Assert and ForEach are definable here, but are made a primitive to
keep their structures.

5. new primitives: array length, null type, store, put, astore

INTERNAL: bottom type 'Tbottom' and null type 'Tnull' are used only internally during
typechecking. It should not be leaked pass 'jtyping.ml'.

- Tbottom <: t for all types (including primitive types like int)
- Tnull <: t for all reference types

Tbottom is useful as the unit type in computing joins, while Tnull
useful in typing the constant 'null'.

*)


type ctask = cunit list      (* compilation task *)
and cunit = package * import list * decl list (* compilation unit *)
and package = id list                   (* package path *)
and block = stmt list                   (* statement block *)
and exps = exp list                     (* expression list *)
and tys = ty list                       (* type list *)
and expo = exp option                   (* expression option *)
and catch = modifiers * ty * id * block (* exception catch *)
and formal = modifiers * ty * id        (* formal argument *)
and import = info * bool * package * id option (* import declaration: static? and all? *)
and modifiers = modifier list           (* type modifier list *)
and tparams = (id * ty * tys) list      (* type parameters *)
and id = string                         (* identifier *)
and info = string                       (* line info *)
and mty = modifiers * ikind * ty * cname * id * tys (* method type *)
and fty = modifiers * ty * cname * id   (* field type *)
and vty = ty * id * int                 (* local variable type *)

and ckind = Cclass | Ciface | Cenum | Cannot (* class kind *)

(* fully-qualified class name (p,xs,x): package, enclosing classes, class identifier *)
and cname = package * id list * id

(* enumeration constant: annotations, identifier, arguments, bodies *)
and enumconst = modifiers * id * exps * body list 

(* method signature: formal arguments, variable arity argument, annotation default, 
array dimension, exception names *)
and signat = formal list * formal option * expo * cname list 

and decl =                              (* type declaration *)
  | Class of info * modifiers * cname * tparams * ty * ty list * body list
  | Iface of info * modifiers * cname * tparams * ty list * body list
  | Enum of info * modifiers * cname * ty list * enumconst list * body list
  | Annot of info * modifiers * cname * body list

and ty =                                (* type *)
  | Tarray of ty * int           (* array *)
  | Tinst of ty * wty list       (* instantiated *)
  | Tcname of cname                     (* fully-qualified name *)
  | Tvar of id * int                    (* variable *)
  | Tbottom                               (* INTERNAL bottom *)
  | Tnull                               (* INTERNAL null *)
  | Tbool
  | Tbyte
  | Tchar
  | Tdouble
  | Tfloat
  | Tint
  | Tlong
  | Tshort
  | Tvoid

and ikind =                              (* invocation ikind *)
  | Iiface                              (* interface *)
  | Ispecial                            (* constructor *)
  | Ivirtual                            (* virtual (normal) *)
  | Istatic                             (* static *)

and wty =                               (* wild card type *)
  | WildType of ty               (* non-wildcard type *)
  | WildCard                     (* plain wildcard *)
  | WildExtends of ty            (* wildcard with upper bound *)
  | WildSuper of ty              (* wildcard with lower bound *)

and body =                              (* declaration body *)
  | Init of info * bool * block            (* initialization *)
  | Inner of info * decl                   (* inner declaration *)
  | Ctor of info * modifiers * tparams * cname * id * signat * block
  | Method of info * modifiers * ikind * tparams * ty * cname * id * signat * block option
  | Field of info * modifiers * ty * cname * id

and stmt =                              (* statement *)
  | Assert of info * cname * exp * expo  (* extra: enclosing class name and type of eo *)
  | Block of info * block
  | Break of info * id option
  | Case of info * exp
  | Continue of info * id option
  | Default of info
  | Do of info * stmt * exp
  | Exp of info * exp
  | ForEach of info * block * ty * id * int * exp * stmt (* block of label statements *)
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

and exp =
  | Array of info * ty * exps           (* array initializer *)  
  | Put of info * bool * expo * fty * P.assign * exp (* put field *)
  | Astore of info * bool * exp * exp * P.assign * exp (* array store *)
  | Store of info * bool * id * int * P.assign * exp (* variable store *)
  | Binary of info * ty * exp * P.binary * exp (* binary operation *)
  | Instof of info * exp * ty           (* instance-of test *)
  | Cond of info * exp * exp * exp      (* conditional *)
  | Cast of info * ty * exp             (* cast *)
  | Neg of info * exp                   (* negative *)
  | Not of info * exp                   (* negation *)
  | Inv of info * exp                   (* inversion *)
  | Aload of info * exp * exp           (* array load *)
  | Length of info * exp                (* array length *)
  | ExpClass of info * ty               (* class type *)
  | Invoke of info * expo * mty * exps  (* method invoke *)
  | True of info                        (* true *)
  | False of info                       (* false *)
  | Null of info                        (* null *)
  | Char of info * string               (* character *)
  | Int of info * int32                (* integer *)
  | Long of info * int64               (* long integer *)
  | Float of info * float              (* floating point *)
  | Double of info * float              (* floating point *)
  | Str of info * string                (* string *)
  | Load of info * ty * id * int        (* load local variable *)
  | Get of info * expo * fty             (* get field *)
  | NewArrNone of info * ty * exps * int (* array creation *)
  | NewArrSome of info * ty * exps (* array creation *)
  | NewObj of info * mty * exps * body list (* object creation *)

(* Datatype copying unsupported in F# *)
(*
and binary = P.binary =                 (* binary operator *)
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
  | Rem                                 (* remainder *)

and assign = P.assign =                           (* assignment operator *)
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
*)

and modifier =                          (* type modifier *)
  | Annotate of info * cname * (id * exp) list
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

let x_eq (x1:id) (x2:id) = x1 = x2

let cname_eq ((xs1,xs2,x):cname) ((ys1,ys2,y):cname) : bool = 
  L.all2 (=) xs1 ys1 && L.all2 (=) xs2 ys2 && x=y

let ty_name_eq (n:cname) : ty -> bool = function
  | Tcname (n2) -> cname_eq n n2
  | _ -> false

let rec ty_eq (t1:ty) (t2:ty) : bool =
  t1 == t2 ||
  match (t1,t2) with
  | (Tarray (t3,n1),Tarray (t4,n2)) -> ty_eq t3 t4 && n1=n2
  | (Tinst (t3,w1),Tinst (t4,w2)) -> 
(*    ty_eq t3 t4 && L.all2 wty_eq w1 w2  (* FIXME: use w1, w2*) *)
    ty_eq t3 t4
  | (Tcname n1, Tcname n2) -> cname_eq n1 n2
  | (Tvar (x1,i1), Tvar (x2,i2)) -> x1=x2 (* FIXME: should use indices i1,i2 instead *)
  | (Tbool,Tbool) -> true
  | (Tbyte,Tbyte) -> true
  | (Tchar,Tchar) -> true
  | (Tdouble,Tdouble) -> true
  | (Tfloat,Tfloat) -> true
  | (Tint,Tint) -> true
  | (Tlong,Tlong) -> true
  | (Tshort,Tshort) -> true
  | (Tvoid,Tvoid) -> true
  | _ -> false

and wty_eq (w1:wty) (w2:wty) : bool =
  match (w1,w2) with
  | (WildType (t1), WildType (t2)) -> ty_eq t1 t2
  | (WildCard , WildCard ) -> true
  | (WildExtends (t1), WildExtends (t2)) -> ty_eq t1 t2
  | (WildSuper (t1), WildSuper (t2)) -> ty_eq t1 t2
  | _ -> false


(*---- Predefined names and types. *)

(* fully-qualified name without enclosing classes *)
let cname_of (n:P.name) : cname =
  let (t,h) = L.tail_head n in (t, [], h)

let read x : cname = cname_of (Strx.read '.' x)

let cobject = read "java.lang.Object"
let cclass = read "java.lang.Class"
let ccloneable = read "java.lang.Cloneable"
let cserializable = read "java.io.Serializable"
let cvoid = read "java.lang.Void"
let cboolean = read "java.lang.Boolean"
let cbyte = read "java.lang.Byte"
let ccharacter = read "java.lang.Character"
let cshort = read "java.lang.Short"
let cinteger = read "java.lang.Integer"
let clong = read "java.lang.Long"
let cfloat = read "java.lang.Float"
let cdouble = read "java.lang.Double"
let cstring = read "java.lang.String"
let cthrowable = read "java.lang.Throwable"
let cerror = read "java.lang.Error"
let citerable = read "java.lang.Iterable"
let citerator = read "java.util.Iterator"
let cassertion = read "java.lang.AssertionError"

let tobject = Tcname cobject
let tclass = Tcname cclass
let tcloneable = Tcname ccloneable
let tserializable = Tcname cserializable
let tvoid = Tcname cvoid
let tboolean = Tcname cboolean
let tbyte = Tcname cbyte
let tcharacter = Tcname ccharacter
let tshort = Tcname cshort
let tinteger = Tcname cinteger
let tlong = Tcname clong
let tfloat = Tcname cfloat
let tdouble = Tcname cdouble
let tstring = Tcname cstring
let tthrowable = Tcname cthrowable
let terror = Tcname cerror
let titerable = Tcname citerable
let titerator = Tcname citerator

let is_object : ty -> bool = function
  | Tcname c -> cname_eq c cobject
  | _ -> false

let is_tvar : ty -> bool = function
  | Tvar _ -> true
  | _ -> false

let is_static (ms:modifiers) : bool = L.mem Static ms


(*---- Erasure from typed to untyped 'to'. *)

let rec ty_to : ty -> P.ty = function
  | Tarray (t,i) -> P.Tarray (ty_to t, i)
  | Tinst (t,ws) -> P.Tinst (ty_to t, L.map wty_to ws)
  | Tcname (xs1,xs2,x) -> P.Tname (cname_to (xs1,xs2,x))
  | Tvar (x,_) -> P.Tname [x]
  | Tbool -> P.Tbool
  | Tbyte -> P.Tbyte
  | Tchar -> P.Tchar
  | Tdouble -> P.Tdouble
  | Tfloat -> P.Tfloat
  | Tint -> P.Tint
  | Tlong -> P.Tlong
  | Tshort -> P.Tshort
  | Tvoid -> P.Tvoid
  | Tnull -> Std.assert_false ()               (* only used in 'Jtyped' *)
  | Tbottom -> Std.assert_false ()               (* only used in 'Jtyped' *)

and wty_to : wty -> P.wty = function
  | WildType (t) -> P.WildType (ty_to t)
  | WildCard -> P.WildCard
  | WildExtends (t) -> P.WildExtends (ty_to t)
  | WildSuper (t) -> P.WildSuper (ty_to t)

and cname_to ((xs1,xs2,x):cname) : P.name = xs1 @ xs2 @ [x]

and ctask_to (t:ctask) : P.ctask = L.map cunit_to t

and cunit_to ((n,is,ds):cunit) : P.cunit =
  (n, L.map import_to is, L.map decl_to ds)

and import_to ((z,b,p,no):import) : P.import = 
  match no with
  | None -> (z, b, p, true)
  | Some n -> (z, b, p @ [n], false)

and decl_to : decl -> P.decl = function
  | Class (z,ms,(_,_,x),ps,t,ts,b) -> 
    P.Class (z, modifiers_to ms, x, L.map tparam_to ps, 
      ty_to t, L.map ty_to ts, L.map body_to b)
  | _ -> Std.assert_false ()

and tparam_to (x,t,ts) = (x, ty_to t, L.map ty_to ts)
and block_to (b:block) : P.block = L.map stmt_to b
and modifiers_to (ms:modifier list) : P.modifier list = L.map modifier_to ms
and catch_to ((ms,t,x,b):catch) : P.catch =
  (modifiers_to ms, ty_to t, x, block_to b)

and formal_to ((ms,t,x):formal) : P.formal =
  (modifiers_to ms, ty_to t, x)

and signat_to ((fs,fo,eo,ns):signat) : P.signat =
  (L.map formal_to fs, opt_map formal_to fo, 
  opt_map exp_to eo, L.map cname_to ns)

and body_to : body -> P.body = function
  | Init (z,x,b) -> P.Init (z, x, block_to b)
  | Inner (z,d) -> P.Inner (z, decl_to d)
  | Ctor (z,ms,ps,_,x,s,b) ->
    P.Ctor (z, modifiers_to ms, L.map tparam_to ps, x, signat_to s, block_to b)
  | Method (z,ms,_,ps,t,_,x,s,bo) -> 
    P.Method (z, modifiers_to ms, L.map tparam_to ps, ty_to t, x, 
      signat_to s, opt_map block_to bo)
  | Field (z,ms,t,_,x) -> 
    P.Field (z, modifiers_to ms, ty_to t, x)

and stmt_to : stmt -> P.stmt = function
  | Assert (z,_,e,eo) -> P.Assert (z, exp_to e, opt_map exp_to eo)
  | Block (z,b) -> P.Block (z, block_to b)
  | Break (z,xo) -> P.Break (z, xo)
  | Case (z,e) -> P.Case (z, exp_to e)
  | Continue (z,xo) -> P.Continue (z,xo)
  | Default z -> P.Default z
  | Do (z,s,e) -> P.Do (z, stmt_to s, exp_to e)
  | Exp (z,e) -> P.Exp (z, exp_to e)
  | ForEach (z,ls,_,x,_,e,s) -> 
    P.ForEach (z, block_to ls, x, exp_to e, stmt_to s)
  | ForExp (z,e,es,s) -> 
    P.ForExp (z, exp_to e, exps_to es, stmt_to s)
  | If (z,e,s1,s2) -> P.If (z, exp_to e, stmt_to s1, stmt_to s2)
  | Label (z,x) -> P.Label (z,x)
  | Local (z,d) -> P.Local (z, decl_to d)
  | Return (z,eo) -> P.Return (z, opt_map exp_to eo)
  | Switch (z,e,b) -> P.Switch (z, exp_to e, block_to b)
  | Sync (z,e,b) -> P.Sync (z, exp_to e, block_to b)
  | Throw (z,e) -> P.Throw (z, exp_to e)
  | Try (z,b1,cs,b2) -> P.Try (z, block_to b1, L.map catch_to cs, block_to b2)
  | Vdecl (z,ms,t,x) -> 
    P.Vdecl (z, modifiers_to ms, ty_to t, x)
  | While (z,e,s) -> P.While (z, exp_to e, stmt_to s)

and modifier_to : modifier -> P.modifier = function
  | Annotate (z,n,s) -> 
    P.Annotate (z, cname_to n, L.map (fun (x,e) -> (x, exp_to e)) s)
  | Abstract -> P.Abstract 
  | Final -> P.Final 
  | Native -> P.Native 
  | Private -> P.Private 
  | Protected -> P.Protected 
  | Public -> P.Public 
  | Static -> P.Static 
  | Strictfp -> P.Strictfp 
  | Synchronized -> P.Synchronized 
  | Transient -> P.Transient 
  | Volatile -> P.Volatile 

and name_to (z:info) (n:P.name) : P.exp =
  let xs = L.map (fun x -> P.Ident (z, x)) n in
  assert (L.size xs > 0);
  L.foldl1 (fun e x -> P.Dot (z, e, x)) xs

and exp_to : exp -> P.exp = function
  | Array (z,_,es) -> P.Array (z, exps_to es)
  | Put (z,p,None,(_,_,_,x),a,e2) -> 
    P.Assign (z, p, P.Ident (z, x), a, exp_to e2)
  | Put (z,p,Some e1,(_,_,_,x),a,e2) -> 
    P.Assign (z, p, P.Dot (z, exp_to e1, P.Ident (z, x)), a, exp_to e2)
  | Store (z,p,x,_,a,e) -> 
    P.Assign (z, p, P.Ident (z, x), a, exp_to e)
  | Astore (z,p,e1,e2,a,e) -> 
    P.Assign (z, p, P.Offset (z, exp_to e1, exp_to e2), a, exp_to e)
  | Binary (z,_,e1,b,e2) -> P.Binary (z, exp_to e1, b, exp_to e2)
  | Instof (z,e,t) -> P.Instof (z, exp_to e, ty_to t)
  | Cond (z,e1,e2,e3) -> P.Cond (z, exp_to e1, exp_to e2, exp_to e3)
  | Cast (z,t,e) -> P.Cast (z, ty_to t, exp_to e)
  | Neg (z,e) -> P.Neg (z, exp_to e)
  | Not (z,e) -> P.Not (z, exp_to e)
  | Inv (z,e) -> P.Inv (z, exp_to e)
  | Aload (z,e1,e2) -> P.Offset (z, exp_to e1, exp_to e2)
  | Get (z,None,(_,_,_,x)) -> P.Ident (z, x)
  | Get (z,Some e,(_,_,_,x)) -> P.Dot (z, exp_to e, P.Ident (z, x))
  | Length (z,e) -> P.Dot (z, exp_to e, P.Ident (z, "length"))
  | ExpClass (z,t) -> P.ExpClass (z, ty_to t)
  | Invoke (z,None,(_,_,_,n,x,_),es) -> 
    P.Invoke (z, P.Dot (z, name_to z (cname_to n), P.Ident (z, x)), exps_to es)
  | Invoke (z,Some e,(_,_,_,_,x,_),es) -> 
    P.Invoke (z, P.Dot (z, exp_to e, P.Ident (z, x)), exps_to es)
  | True z -> P.True z
  | False z -> P.False z
  | Null z -> P.Null z
  | Char (z,s) -> P.Char (z,s)
  | Int (z,s) -> P.Int (z,s)
  | Long (z,s) -> P.Long (z,s)
  | Float (z,s) -> P.Float (z,s)
  | Double (z,s) -> P.Double (z,s)
  | Str (z,s) -> P.Str (z,s)
  | Load (z,_,x,_) -> P.Ident (z,x)
  | NewArrNone (z,t,es,i) -> P.NewArrNone (z, ty_to t, exps_to es, i)
  | NewArrSome (z,t,es) -> P.NewArrSome (z, ty_to t, exps_to es)
  | NewObj (z,(_,_,_,n,_,_),es,bs) -> 
    P.NewObj (z, cname_to n, [], exps_to es, L.map body_to bs)

and exps_to (es:exps) : P.exps = L.map exp_to es


(*---- Show. *)

(* java.lang.Boolean$C$D$E -> (["java";"lang";"Boolean"],["C";"D"],"E") *)
let cname_read (x:string) : cname = 
  match Strx.read '$' x with
  | [] -> Std.assert_false () (* INVARIANT: Strx.read *)
  | [y] -> let (t,h) = L.tail_head (Strx.read '.' y) in (t, [], h)
  | y::ys -> let (t,h) = L.tail_head ys in (Strx.read '.' y, t, h)

let show format = Printf.sprintf format

let rec ctask_show (t:ctask) : string = 
  L.show "\n----\n" cunit_show t

and cunit_show ((no,is,ds):cunit) : string = 
  show "%s%s%s\n" (package_show no)
  (if is=[] then "" else L.show1 import_show is ^ "\n\n") 
  (L.show2 decl_show ds)

and package_show n = 
  if n=[] then "" else showf "package %s;\n\n" (P.name_show n)

and import_show i = P.import_show (import_to i)

and cname_showx ((p,cs,x):cname) : string =
  showf "(%s # %s # %s)" (L.show "/" id_show p) (L.show "." id_show cs) x

and cname_show ((p,cs,x):cname) = 
  Strx.suffix_with "/" p ^ Strx.suffix_with "$" cs ^ x

and id_show x : string = x

and decl_show = function
  | Class (_,x0,x1,x2,x3,x4,x5) -> 
    show "%sclass %s%s%s%s %s" (modifiers_show x0)
   (cname_show x1) (tparams_show x2) (extend_show x3) 
   (implements_show x4) (bodies_show x5)
  | Iface (_,x0,x1,x2,x3,x4) ->
    show "%sinterface %s%s%s %s" (modifiers_show x0) 
    (cname_show x1) (tparams_show x2) (extends_show x3) (bodies_show x4)
  | Enum (_,x0,x1,x2,x3,x4) ->
    show "%senum %s %s { %s %s }" (modifiers_show x0)
    (cname_show x1) (implements_show x2) (L.show1 enumconst_show x3) (bodies_show x4)
  | Annot (_,x0,x1,x2) -> 
    show "%s@@interface %s %s" (modifiers_show x0) (cname_show x1) (bodies_show x2)

and tparams_show x0 = 
  if x0=[] then "" else show "<%s>" (L.show "," tparam_show x0)

and tparam_show (x0,x1,x2) = 
  show "%s%s%s" (id_show x0) (extend_show x1) (L.showz tinter_show x2)

and tinter_show x0 = show "& %s" (ty_show x0)

and targs_show x0 = if x0=[] then "" else show "<%s>" (L.show "," wty_show x0)

and wty_show = function
  | WildType (x0) -> show "%s" (ty_show x0)
  | WildCard -> show "?" 
  | WildExtends (x0) -> show "? extends %s" (ty_show x0)
  | WildSuper (x0) -> show "? super %s" (ty_show x0)

and extend_show (t:ty) : string = 
  if is_object t then "" else show " extends %s" (ty_show t)

and extends_show x0 = 
  if x0=[] then "" else show " extends %s" (L.show "," ty_show x0)

and implements_show x0 = 
  if x0=[] then "" else show " implements %s" (L.show ", " ty_show x0)

and ty_show = function
  | Tarray (x0,x1) -> show "%s%s" (ty_show x0) (dimen_show x1)
  | Tinst (x0,x1) -> show "%s%s" (ty_show x0) (targs_show x1)
  | Tcname (x0) -> show "%s" (cname_show x0)
  | Tvar (x,i) -> show "%s/%d" x i
  | Tbool -> show "boolean" 
  | Tbyte -> show "byte" 
  | Tchar -> show "char" 
  | Tdouble -> show "double" 
  | Tfloat -> show "float" 
  | Tint -> show "int" 
  | Tlong -> show "long" 
  | Tshort -> show "short" 
  | Tvoid -> show "void" 
  | Tnull -> show "null" 
  | Tbottom -> show "bottom" 

and ty_showx = function
  | Tarray (x0,x1) -> show "%s%s" (ty_show x0) (dimen_show x1)
  | Tinst (x0,x1) -> show "%s%s" (ty_show x0) (targs_show x1)
  | Tcname (x0) -> show "%s" (cname_showx x0)
  | Tvar (x,i) -> show "%s/%d" x i
  | Tbool -> show "boolean" 
  | Tbyte -> show "byte" 
  | Tchar -> show "char" 
  | Tdouble -> show "double" 
  | Tfloat -> show "float" 
  | Tint -> show "int" 
  | Tlong -> show "long" 
  | Tshort -> show "short" 
  | Tvoid -> show "void" 
  | Tnull -> show "null" 
  | Tbottom -> show "bottom" 

and dimen_show i = Strx.repeat i "[]" 

and body_show = function
  | Init (_,x0,x1) ->
    show "%s %s" (if_show "static" x0) (block_show x1)
  | Inner (_,x0) ->
    show "%s" (decl_show x0)
  | Ctor (_,x0,x1,c,x2,x3,x4) ->
    show "%s%s%s.%s%s %s" (modifiers_show x0) (tparams_show x1) (cname_show c) (id_show x2) 
    (signat_show x3) (block_show x4)
  | Method (_,x0,k,x1,x2,c,x3,x4,None) ->
    show "%s[%s]%s%s %s.%s%s;" (modifiers_show x0) (ikind_show k)
      (tparams_show x1) (ty_show x2) (cname_show c) (id_show x3) (signat_show x4)
  | Method (_,x0,k,x1,x2,c,x3,x4,Some x5) ->
    show "%s[%s]%s%s %s.%s%s%s" (modifiers_show x0) (ikind_show k) (tparams_show x1)
      (ty_show x2) (cname_show c) (id_show x3) (signat_show x4)(block_show x5)
  | Field (_,x0,x1,c,x2) ->
    show "%s%s %s.%s;" (modifiers_show x0) (ty_show x1) (cname_show c) (id_show x2)

and enumconst_show ((ms,x0,x1,x2):enumconst) =
  show "%s%s %s %s" (modifiers_show ms) x0 (arg_show x1) (bodies_show x2)

and bodies_show x0 = 
  if x0=[] then "{\n}" else show "{\n%s\n}" (L.show2 body_show x0)

and signat_show (x0,x,x1,x3) = 
  show " (%s%s)%s%s" (L.show  ", " formal_show x0) (opt_show vararg_show x)
  (opt_show default_show x1) (throws_show x3)

and default_show x0 = show "default %s" (exp_show x0)

and arg_show (x0:exps) = show "(%s)" (L.show ", " exp_show x0)

and modifiers_show x = if x=[] then "" else L.showz modifier_show x ^ " "

and stmt_show = function
  | ForEach (_,ls,t,x2,i,x3,x4) ->
    show "%sfor (%s:%s/%d : %s) %s" (L.showz stmt_show ls) 
      (id_show x2) (ty_show t) i (exp_show x3) (stmt_show x4)
  | ForExp (_,x1,x2,x3) ->
    show "for (; %s; %s) %s" (exp_show x1) (L.show "," exp_show x2) (stmt_show x3)
  | While (_,x0,x1) ->
    show "while (%s) %s" (exp_show x0) (stmt_show x1)
  | If (_,x0,x1,Block (_,[])) ->
    show "if (%s) %s" (exp_show x0) (stmt_show x1) 
  | If (_,x0,x1,x2) ->
    show "if (%s) %s else %s" (exp_show x0) (stmt_show x1) (stmt_show x2)
  | Assert (_,n,x0,None) ->
    show "assert [%s] %s;" (cname_show n) (exp_show x0)
  | Assert (_,n,x0,Some x1) ->
    show "assert %s : %s;" (exp_show x0) (exp_show x1)
  | Block (_,x0) ->
    show "%s" (block_show x0)
  | Break (_,x0) ->
    show "break%s;" (opt_space_show id_show x0)
  | Case (_,x0) ->
    show "case %s:" (exp_show x0)
  | Continue (_,x0) ->
    show "continue%s;" (opt_space_show id_show x0)
  | Vdecl (_,x0,x1,x2) ->
    show "%s%s %s;" (modifiers_show x0) (ty_show x1) (id_show x2)
  | Default (_) ->
    show "default:" 
  | Do (_,x0,x1) ->
    show "do %s while (%s);" (stmt_show x0) (exp_show x1)
  | Exp (_,x0) ->
    show "%s;" (exp_show x0)
  | Label (_,x0) ->
    show "%s:" (id_show x0)
  | Local (_,x0) ->
    show "%s" (decl_show x0)
  | Return (_,x0) ->
    show "return%s;" (opt_space_show exp_show x0)
  | Switch (_,x0,x1) ->
    show "switch (%s) %s" (exp_show x0) (block_show x1)
  | Sync (_,x0,x1) ->
    show "synchronized (%s) %s" (exp_show x0) (block_show x1)
  | Throw (_,x0) ->
    show "throw %s;" (exp_show x0)
  | Try (_,x0,x1,x2) ->
    show "try %s %s%s" (block_show x0) (L.show1 catch_show x1) (finally_show x2)

and block_show x0 = 
  if x0=[] then "{\n}" else show "{\n%s\n}" (L.show1 stmt_show x0)

and catch_show (ms,x,x0,x1) = 
  show "catch (%s%s %s) %s" (modifiers_show ms) 
  (ty_show x) (id_show x0) (block_show x1)

and finally_show x0 = 
  if x0=[] then "" else show " finally %s" (block_show x0)

and throws_show x0 = 
  if x0=[] then "" else show " throws %s" (L.show ", " cname_show x0)

and formal_show (x0,x1,x2) = 
  show "%s%s %s" (modifiers_show x0) (ty_show x1) (id_show x2) 

and vararg_show (x0,x1,x2) = 
  show ", %s%s... %s" (modifiers_show x0) (ty_show x1) (id_show x2)

and exp_show : exp -> string = function
  | Array (_,t,x0) ->
    show "[%s]{ %s }" (ty_show t) (L.show ", " exp_show x0)
  | Put (_,p,e1,f,a,e2) ->
    show "[%s] %s.%s %s %s" (if p then "pre" else "post")
      (expo_show e1) (fty_show f) (assign_show a) (exp_show e2)
  | Store (_,p,x,i,x1,x2) ->
    show "[%s] %s/%d %s %s" (if p then "pre" else "post")
      (id_show x) i (assign_show x1) (exp_show x2)
  | Astore (_,p,e1,e2,x1,x2) ->
    show "[%s] %s[%s] %s %s" (if p then "pre" else "post")
      (exp_show e1) (exp_show e2) (assign_show x1) (exp_show x2)
  | Cond (_,e1,True _,e2) -> show "%s || %s" (exp_show e1) (exp_show e2)
  | Cond (_,e1,e2,False _) -> show "%s && %s" (exp_show e1) (exp_show e2)
  | Cond (_,x0,x1,x2) ->
    show "%s ? %s : %s" (exp_show x0) (exp_show x1) (exp_show x2)
  | Binary (_,t,x1,x2,x3) ->
    show "[%s] %s %s %s" (ty_show t) (exp_show x1) (binary_show x2) (exp_show x3)
  | Instof (_,x0,x1) ->
    show "%s instanceof %s" (exp_show x0) (ty_show x1)
  | Cast (_,x0,x1) ->
    show "(%s)%s" (ty_show x0) (exp_show x1)
  | Neg (_,x0) ->
    show "-%s" (exp_show x0)
  | Not (_,x0) ->
    show "!%s" (exp_show x0)
  | Inv (_,x0) ->
    show "~%s" (exp_show x0)
  | Aload (_,x0,x1) ->
    show "%s[%s]" (exp_show x0) (exp_show x1)
  | Get (_,e,f) ->
    show "(%s).(%s)" (expo_show e) (fty_show f)
  | Length (_,e) ->
    show "%s.length" (exp_show e)
  | ExpClass (_,x0) ->
    show "%s.class" (ty_show x0)
  | Invoke (_,None,x0,x1) ->
    show "(%s)%s" (mty_show x0) (arg_show x1)
  | Invoke (_,Some e,x0,x1) ->
    show "(%s).(%s)%s" (exp_show e) (mty_show x0) (arg_show x1)
  | True _ ->
    show "true" 
  | False _ ->
    show "false" 
  | Null _ ->
    show "null" 
  | Char (_,x0) -> "'" ^ x0 ^ "'"
  | Long (_,x0) -> int64_show x0 ^ "l"
  | Int (_,x0) -> int32_show x0
  | Float (_,x0) -> float_show x0 ^ "f"
  | Double (_,x0) -> float_show x0 ^ "d"
  | Str (_,x) -> Strx.code x
  | Load (_,t,x,i) -> vty_show (t,x,i)
  | NewArrNone (_,t,es,i) ->
    show "new (%s)%s %s" (ty_show t) (L.show0 size_show es) (dimen_show i)
  | NewArrSome (_,t,es) ->
    show "new %s { %s }" (ty_show t) (L.show "," exp_show es)
  | NewObj (_,mty,es,bs) ->
    show "new %s%s%s" (mty_show mty) (arg_show es) 
    (opt_list_show bodies_show bs)

and vty_show ((t,x,i):vty) : string =
  show "%s:%s/%d" (id_show x) (ty_show t) i

and ckind_show = function
  | Cclass -> "class"
  | Ciface -> "interface"
  | Cenum -> "enum"
  | Cannot -> "annotation"

and expo_show : expo -> string = function
  | None -> ""
  | Some e -> exp_show e

and fty_show ((ms,t,n,x):fty) : string = 
  showf "(%s%s,%s,%s)" (modifiers_show ms)
    (ty_show t) (cname_show n) (id_show x)

and size_show e = show "[%s]" (exp_show e)

and assign_show = function
  | P.Set -> "=" 
  | P.AddSet -> "+=" 
  | P.SubSet -> "-=" 
  | P.MulSet -> "*=" 
  | P.DivSet -> "/=" 
  | P.RemSet -> "%%=" 
  | P.AndSet -> "&=" 
  | P.OrSet -> "|=" 
  | P.XorSet -> "^=" 
  | P.ShlSet -> "<<=" 
  | P.ShrSet -> ">> =" 
  | P.UshrSet -> ">>> =" 

and binary_show = function
  | P.Or -> "|"
  | P.Xor -> "^"
  | P.And -> "&"
  | P.Eq -> "=="
  | P.Ne -> "!="
  | P.Lt -> "<"
  | P.Gt -> ">"
  | P.Le -> "<="
  | P.Ge -> ">="
  | P.Shl -> "<<"
  | P.Shr -> ">>"
  | P.Ushr -> ">>>"
  | P.Add -> "+"
  | P.Sub -> "-"
  | P.Mul -> "*"
  | P.Div -> "/"
  | P.Rem -> "%"

and modifier_show = function
  | Annotate (_,x0,[]) -> show "@@%s" (cname_show x0)
  | Annotate (_,x0,[("value",e)]) -> 
    show "@@%s(%s)" (cname_show x0) (exp_show e)
  | Annotate (_,x0,x1) ->
    show "@@%s(%s)" (cname_show x0) (L.show "," labelexp_show x1)
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

and labelexp_show (x0,x1) = show "%s = %s" (id_show x0) (exp_show x1)

and ikind_show : ikind -> string = function
  | Iiface -> "interface"
  | Ispecial -> "special"
  | Ivirtual -> "virtual"
  | Istatic -> "static"

and mty_show ((ms,k,t,n,x,ts):mty) : string =
  showf "%s[%s] %s %s.%s(%s)" (modifiers_show ms)
    (ikind_show k) (ty_show t) (cname_show n) (id_show x)
    (L.show "," ty_show ts)

and mty_showx ((ms,k,t,n,x,ts):mty) : string =
  showf "%s[%s] %s %s.%s(%s)" (modifiers_show ms)
    (ikind_show k) (ty_showx t) (cname_showx n) (id_show x)
    (L.show "," ty_show ts)


(*---- Info *)

let exp_info (e:exp) : info = P.exp_info (exp_to e)
let decl_info (d:decl) : info = P.decl_info (decl_to d)



(*---- Accessors. *)

(* type membership *)
let ty_mem (t:ty) (ts:tys) : bool = L.some (ty_eq t) ts

let decl_x : P.decl -> id = function
  | P.Class (_,_,x,_,_,_,_) -> x
  | P.Iface (_,_,x,_,_,_) -> x
  | P.Enum (_,_,x,_,_,_) -> x
  | P.Annot (_,_,x,_) -> x

let decl_modifiers : P.decl -> P.modifiers = function
  | P.Class (_,ms,_,_,_,_,_) -> ms
  | P.Iface (_,ms,_,_,_,_) -> ms
  | P.Enum (_,ms,_,_,_,_) -> ms
  | P.Annot (_,ms,_,_) -> ms

let decl_is_class : P.decl -> bool = function
  | P.Class _ -> true | _ -> false

let decl_is_iface : P.decl -> bool = function
  | P.Iface _ -> true | _ -> false

let body_field_x : P.body -> id option = function
  | P.Field (_,_,_,x) -> Some x
  | _ -> None

let decl_bodies : P.decl -> P.body list = function
  | P.Class (_,_,_,_,_,_,bs) -> bs
  | P.Iface (_,_,_,_,_,bs) -> bs
  | P.Enum (_,_,_,_,_,bs) -> bs
  | P.Annot (_,_,_,bs) -> bs

let ty_is_cname : ty -> bool = function
  | Tcname _ -> true 
  | _ -> false

let rec ty_cname : ty -> cname = function
  | Tcname n -> n
  | Tinst (t,_) -> ty_cname t           (* FIXME *)
  | Tarray (t,_) -> ty_cname t
  | t -> printl (ty_show t); (* todo *) Std.assert_false ()

(*
let decl_bounds : P.decl -> tys = function
  | P.Class (_,_,_,_,t,ts,_) -> tys_of (t :: ts)
  | P.Iface (_,_,_,_,ts,_) -> tys_of ts
  | P.Enum (_,_,_,ts,_,_) -> tys_of ts
  | P.Annot _ -> [tannotation]
*)

let bounds_show (ts:tys) : string = 
  if ts=[] then "" else "<:" ^ L.show "&" ty_show ts


(*-- misc *)

(* push array dimension into the type *)
let array_type (t:ty) (n:int) = 
  match (t,n) with
  | (_,0) -> t
  | (Tarray (t2,n2),_) -> Tarray (t2,n2+n)
  | _ -> Tarray (t,n)

(* base type of array type *)
let array_base : ty -> ty = function
  | Tarray (t,n) -> if n=1 then t else Tarray (t,n-1)
  | t -> error "not array type: %s" (ty_show t)

(* base type of array or iterable type *)
let array_iterable_base : ty -> ty = function
  | Tarray (t,n) -> if n=1 then t else Tarray (t,n-1)
  | Tinst (t1,[WildType t2]) when ty_name_eq citerable t1 -> t2
  | t -> error "not array type: %s" (ty_show t)

(*--- type of an expression *)

let rec exp_ty : exp -> ty = function
  | Put (_,_,_,(_,t,_,_),_,_) -> t
  | Astore (_,_,_,_,_,e) -> exp_ty e
  | Store (_,_,_,_,_,e) -> exp_ty e
  | Neg (_,e) -> exp_ty e 
  | Not (_,e) -> exp_ty e 
  | Inv (_,e) -> exp_ty e 
  | Cond (_,_,e,_) -> exp_ty e
  | Binary (_,t,_,_,_) -> t
  | Cast (z,t,_) -> t
  | Array (_,t,_) -> t
  | Load (_,t,_,_) -> t 
  | Get (_,_,(_,t,_,_)) -> t 
  | Length _ -> Tint 
  | Invoke (_,_,(_,_,t,_,_,_),_) -> t
  | Instof _ -> Tbool
  | True _ -> Tbool
  | False _ -> Tbool
  | Null _ -> Tnull
  | Char (_,s) -> Tchar
  | Int (_,s) -> Tint
  | Long (_,s) -> Tlong
  | Float (_,s) -> Tfloat
  | Double (_,s) -> Tdouble
  | Str (z,s) -> Tcname cstring
  | ExpClass (z,t) -> Tcname cclass
  | Aload (_,e,_) -> array_base (exp_ty e)
  | NewArrNone (z,t,_,_) -> t            (* FIXME: use ws *)
  | NewArrSome (z,t,_) -> t            (* FIXME: use ws *)
  | NewObj (z,(_,_,_,c,_,_),_,_) -> Tcname c

and modifier_of : P.modifier -> modifier = function
  | P.Annotate (z,n,s) -> (* todo *) Std.assert_false () (* move this to jtyping *)
  | P.Abstract -> Abstract 
  | P.Final -> Final 
  | P.Native -> Native 
  | P.Private -> Private 
  | P.Protected -> Protected 
  | P.Public -> Public 
  | P.Static -> Static 
  | P.Strictfp -> Strictfp 
  | P.Synchronized -> Synchronized 
  | P.Transient -> Transient 
  | P.Volatile -> Volatile 

and modifiers_of (ms:P.modifier list) : modifier list = L.map modifier_of ms


(* Accessories functions *)

let ty_is_prim : ty -> bool = function
  | Tbool | Tbyte | Tchar | Tdouble 
  | Tfloat | Tint | Tlong | Tshort | Tvoid -> true
  | _ -> false

let vararg_of : formal option -> formal list = function
  | None -> []
  | Some (ms,t,x) -> [(ms, array_type t 1, x)]
