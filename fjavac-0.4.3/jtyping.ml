(* jtyping.ml - java typing (from plain syntax trees to typed syntax trees) *)

open Std
open Jtyped
module G = Jenv
module L = Listx
module P = Jplain

exception Fail


(*---- type checking 'ck' and 'ty' *)

(* Is valid field modifier JLS 8.3.1 *)
let is_field_modifier : modifier -> bool = function
  | Annotate _ | Private | Protected | Public 
  | Final | Static | Transient | Volatile -> true
  | Native | Strictfp | Synchronized | Abstract -> false

(* Is valid variable modifier JLS 8.3.1 *)
let is_variable_modifier : modifier -> bool = function
  | Annotate _ | Final -> true
  | Private | Protected | Public | Static | Transient | Volatile
  | Native | Strictfp | Synchronized | Abstract -> false

(* Is valid constant modifier JLS 8.3.1 *)
let is_constant_modifier : modifier -> bool = function
  | Annotate _ | Public | Final | Static -> true
  | Transient | Volatile | Private | Protected 
  | Native | Strictfp | Synchronized | Abstract -> false

(* Is valid method modifier *)
let is_method_modifier : modifier -> bool = function
  | Annotate _ | Private | Protected | Public 
  | Final | Static | Native | Synchronized
  | Strictfp |  Abstract -> true
  | Transient | Volatile -> false

(* Is valid abstract method modifier *)
let is_abstract_modifier : modifier -> bool = function
  | Annotate _ | Public | Abstract -> true
  | Private | Protected | Strictfp
  | Final | Static  | Native | Synchronized  
  | Transient | Volatile -> false

(* Is valid constructor modifier *)
let is_ctor_modifier : modifier -> bool = function
  | Annotate _ | Private | Protected | Public -> true
  | Final | Static  | Native | Synchronized
  | Strictfp |  Abstract | Transient | Volatile -> false

(* Is valid class modifier *)
let is_class_modifier : modifier -> bool = function
  | Annotate _ | Private | Protected | Public 
  | Abstract | Final | Static | Strictfp -> true
  | Transient | Volatile | Native  | Synchronized  -> false

(* Is valid interface modifier *)
let is_iface_modifier : modifier -> bool = function
  | Annotate _ | Private | Protected | Public 
  | Abstract | Static | Strictfp -> true
  | Final | Transient | Volatile | Native  | Synchronized  -> false


(*--- Tying *)


let ck_xs_uniq (z:info) (xs:id list) (msg:string) : unit =    
  match L.dup1_by x_eq xs with
  | Some s -> error "%s: duplicate %s: %s" z msg s
  | None -> ()

let ck_ts_uniq (z:info) (ts:ty list) (msg:string) : unit =    
  match L.dup1_by ty_eq ts with
  | Some t -> error "%s: duplicate %s: %s" z msg (ty_show t)
  | None -> ()

let ck_modifiers (z:info) (f:modifier -> bool) (ms:modifiers) : unit =
  (match L.dup1 ms with
  | Some m -> error "%s: duplicate modifier: %s" z (modifier_show m)
  | None -> ());
  match L.find (flip f) ms with
  | Some m -> error "%s: invalid modifier: %s" z (modifier_show m)
  | None -> ()

let ck_formals (z:info) (fs:formal list) : unit =
  (match L.dup1 (L.map get3 fs) with
  | Some s -> error "%s: duplicate parameter: %s" z s
  | None -> ());
  L.iter (fun (ms,_,_) -> ck_modifiers z is_variable_modifier ms) fs


(*---- subtyping *)

let ty_is_ref : ty -> bool = function
  | Tarray _ 
  | Tinst _
  | Tcname _ -> true
  | _ -> false


let rec subty (z:info) (g:G.t) (t1:ty) (t2:ty) : bool = 
(*  printf "subtyping: %s <: %s\n" (ty_show t1) (ty_show t2); *)
  let f1 t ts = (ty_eq t1 t && ty_mem t2 ts) in (* transitive  *)
  let f2 u1 u2 = (ty_name_eq u1 t1 && ty_eq u2 t2) (* equation *)
    || (ty_name_eq u1 t2 && ty_eq u2 t1) in 
  ty_eq t1 t2                           (* reflexive *)
  || ty_eq t1 Tbottom                   (* bottom *)
  || ty_eq t1 Tnull && ty_is_ref t2     (* null *)
  || ty_is_ref t1 && is_object t2       (* object *)

  (* transitivity of byte <: short <: int <: long <: float <: double *)
  || f1 Tbyte [Tshort; Tint; Tlong; Tfloat; Tdouble]
  || f1 Tshort [Tint; Tlong; Tfloat; Tdouble]
  || f1 Tint [Tlong; Tfloat; Tdouble]
  || f1 Tlong [Tfloat; Tdouble]
  || f1 Tfloat [Tdouble]

  (* transitivity of char <: int <: long <: float <: double *)
  || f1 Tchar [Tint; Tlong; Tfloat; Tdouble]

  (* equation of boxing and unboxing *)
  || f2 cboolean Tbool
  || f2 cbyte Tbyte
  || f2 ccharacter Tchar
  || f2 cdouble Tdouble
  || f2 cfloat Tfloat
  || f2 cinteger Tint
  || f2 clong Tlong
  || f2 cshort Tshort

  || (not (is_object t1) &&         (* inheritance *)
      match (t1,t2) with 
      | (Tinst (t3,_),t4) -> subty z g t3 t4 (* FIXME: comparsion between raw types *)
      | (t3,Tinst (t4,_)) -> subty z g t3 t4
      | (Tarray _,Tcname n) when L.mem n
        [cobject; ccloneable; cserializable] -> true
      | (Tarray (t3,n1), Tarray (t4,n2)) -> n1 = n2 && subty z g t3 t4
      | (Tcname n1,Tcname n2) -> 
        L.some (fun n -> subty z g (Tcname n) t2) (G.super z g n1 :: G.ifaces g n1)
      | _ -> false)

let mty_st (z:info) (g:G.t) ((_,_,_,_,_,ts1):mty) ((_,_,_,_,_,ts2):mty) : bool =
  L.all2 (subty z g) ts1 ts2

(* check if subtype. *)
let ck_st (g:G.t) (e:exp) (t:ty) : unit =
  let t0 = exp_ty e in
  if not (subty (exp_info e) g t0 t)
  then error "%s: subtype error: %s <: %s" (exp_info e) (ty_show t0) (ty_show t)

let ck_st0 (z:info) (g:G.t) (t1:ty) (t2:ty) : unit =
  if not (subty z g t1 t2)
  then error "%s: subtype error: %s <: %s" z (ty_show t1) (ty_show t2)

let ty_is_iface (g:G.t) (t:ty) : bool = 
  ty_is_cname t && (G.kind g (ty_cname t) = Ciface)

(* check if t1 is convertible to t2. *)
let ck_conv (z:info) (g:G.t) (t1:ty) (t2:ty) : unit =
  if not (is_tvar t1 || is_tvar t2 || ty_is_iface g t2 || subty z g t1 t2 || subty z g t2 t1)
  then error "%s: types not comparable: %s, %s" z (ty_show t1) (ty_show t2)

(* FIXME: prove t1 <: t2 && t2 <: t1 impies t1 = t2 *)
let ck_eq (z:info) (g:G.t) (t1:ty) (t2:ty) : unit =
  if not (subty z g t1 t2 && subty z g t2 t1)
  then error "%s: types not equal: %s, %s" z (ty_show t1) (ty_show t2)

(* iterable or array for the new for-each loop construct: t2 = t1[] *)
let ck_iter (z:info) (g:G.t) (t1:ty) (t2:ty) : unit =  
  let t = array_iterable_base t2 in
  if not (subty z g t t1)                  (* contravariant *)
  then error "%s: subtype error: %s <: %s" z (ty_show t2) (ty_show t1)

let is_stringable : ty -> bool = function
  | Tchar -> true
  | Tcname n -> cname_eq cstring n
  | _ -> false

(* small integer *)
let is_small_int : ty -> bool = function
  | Tshort | Tbyte | Tchar -> true
  | _ -> false

let join2 (z:info) (g:G.t) (t1:ty) (t2:ty) : ty =
  if subty z g t1 t2 then t2
  else if subty z g t2 t1 then t1
  else if is_small_int t1 && is_small_int t2 then Tint
  else Tcname cobject

let join (z:info) (g:G.t) (ts:ty list) : ty =
  L.foldl (join2 z g) Tbottom ts


(*---- overloading resolution *)

(* JLS 15.12.2.5 Choosing the Most Specific Method *)
let mty_choose (z:info) (g:G.t) (c:cname) (ts:mty list) : mty = 
  match L.find (fun t -> L.all (mty_st z g t) ts) ts with
  | Some t -> t
  | None -> error "%s: No most specific method among these candidates in class %s:\n%s"
    z (cname_show c) (L.show1 mty_show ts) (* TODO: possible? *)   

(* JLS 15.12 Compile-Time Step 2: Determine Method Signature *)
(* FIXME: BUG: method resolution should use the return type as well? 
   java/lang/Math.java *)
let method_resolve (z:info) (g:G.t) (c:cname) (x:id) (ts:ty list) : mty =
  let n = L.size ts in
  let mts = G.methods g c x in
  (* contravariant *)
  match L.take (fun (_,_,_,_,_,ts2) -> L.all2 (subty z g) ts ts2) mts with
  | [] -> error "%s: no matching method '%s' of arity %d for (%s) \
in class %s, given %d candidates:\n%s" 
    z (id_show x) n (L.show "," ty_show ts) (cname_show c) (L.size mts)
    (L.show1 mty_show mts)
  | [t] -> t
  | ts -> mty_choose z g c ts

let ctor_resolve (z:info) (g:G.t) (c:cname) (ts:ty list) : mty =
  let m = L.size ts in
  let mts = G.methods g c "<init>" in
  (* contravariant *)
  match L.find (fun (_,_,_,_,_,ts2) -> L.all2 (subty z g) ts ts2) mts with 
  | Some t -> t
  | None -> error "%s: no matching constructor \
of arity %d for (%s) in class %s, given %d candidates:\n%s" 
    z m (L.show "," ty_show ts) (cname_show c)
    (L.size mts) (L.show1 mty_show mts)


(*---- Conversion from untyped 'of'. *)

(* Cast expression 'e' to have type 't'. *)
let cast (g:G.t) (e:exp) (t:ty) : exp =
  let t0 = exp_ty e in
  if not (ty_is_prim t) || ty_eq t0 t then e 
  else Cast (exp_info e, t, e)

let ty_one (z:info) : ty -> exp = function
  | Tint -> Int (z, 1l)
  | Tlong -> Long (z, 1L)
  | _ -> (* todo *) Std.assert_false () 

let rec ctask_of (t:P.ctask) : ctask = 
  let g1 = G.ctask_of t in
  let g2 = G.import_all g1 ["java";"lang"] [] in (* default import *)
  L.map (cunit_of g2) t

and cunit_of (g:G.t) ((p,is,ds):P.cunit) : cunit = 
  let g2 = G.imports_of (G.package_of g p) is in
  (p, L.map (import_of g) is, L.map (decl_of g2) ds)

and import_of (g:G.t) ((z,b1,n,b2):P.import) : import =
  let (t,h) = L.tail_head n in
  if b2 then (z, b1, n, None)
  else (z, b1, t, Some h)

and extend_of (z:info) (g:G.t) (t:ty) : unit =
  check (ty_is_cname t) "%s: in 'extends': type '%s' is not a name" z (ty_show t);
  let n = ty_cname t in
(* FIXME rt.jar
  check (G.kind g n = Cclass)
    "%s: type '%s' is not a class (cannot be extended)" z (ty_show t); *)
  check (not (L.mem Final (G.mods g n)))
    "%s: type '%s' is final (cannot be extended)" z (ty_show t)

and ty_of (z:info) (g:G.t) : P.ty -> ty = function
  | P.Tarray (t,i) -> Tarray (ty_of z g t, i)
  | P.Tinst (t,ws) -> Tinst (ty_of z g t, L.map (wty_of z g) ws)
  | P.Tname n -> G.name_of_ty z g n
  | P.Tbool -> Tbool
  | P.Tbyte -> Tbyte
  | P.Tchar -> Tchar
  | P.Tdouble -> Tdouble
  | P.Tfloat -> Tfloat
  | P.Tint -> Tint
  | P.Tlong -> Tlong
  | P.Tshort -> Tshort
  | P.Tvoid -> Tvoid

and tys_of (z:info) (g:G.t) (ts:P.tys) : tys = L.map (ty_of z g) ts

and wty_of (z:info) (g:G.t) : P.wty -> wty = function
  | P.WildType (t) -> WildType (ty_of z g t)
  | P.WildCard -> WildCard 
  | P.WildExtends (t) -> WildExtends (ty_of z g t)
  | P.WildSuper (t) -> WildSuper (ty_of z g t)

and modifier_of (g:G.t) : P.modifier -> modifier = function
  | P.Annotate (z,n,s) -> 
(*    Annotate (z, G.name_of z g n, L.map (fun (x,e) -> (x, exp_of g e)) s) FIXME *) 
    Annotate (z, G.name_of z g n, [])
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

and tparam_of (z:info) (g:G.t) (x,t,ts) = (x, ty_of z g t, tys_of z g ts)

and modifiers_of (g:G.t) (ms:P.modifier list) : modifier list = 
  L.map (modifier_of g) ms

and formal_of (z:info) (g:G.t) ((ms,t,x):P.formal) : formal =
  (modifiers_of g ms, ty_of z g t, x)

and decl_of (g:G.t) : P.decl -> decl = function
  | P.Class (z,ms,x1,ps,t,ts,bs) ->
    let ms2 = modifiers_of g ms in
    let ps2 = L.map (tparam_of z g) ps in
    let t2 = ty_of z g t in
    let ts2 = tys_of z g ts in
    ck_modifiers z is_class_modifier ms2;

    (* BSS: 4.1.1: this *)
    check (not (L.mem Final ms2 && L.mem Abstract ms2))
      "%s: a class cannot be both final and abstract" z;

    (* BSS: 4.1.1: extension *)
    extend_of z g t2;

    (* BSS: 4.1.1: implementatons *)
    check (L.all (fun t -> G.kind g (G.name_of z g (P.ty_name t)) = Ciface) ts)
      "%s: some implementation type is not an interface" z;

    ck_ts_uniq z ts2 "interface type";    
    ck_xs_uniq z (L.collect P.body_field_x bs) "field name";

    (* BSS: 4.1.3: TODO acyclic inheritance *)
    (* BSS: 4.1.4: TODO package and accessibility *)
    let g2 = G.enter_class g x1 in
    let bs2 = L.map (body_of g2) bs in
    Class (z, ms2, G.this g2, ps2, t2, ts2, bs2)

  | P.Iface (z,ms,x,ps,ts,bs) ->
    let ms2 = modifiers_of g ms in
    let ps2 = L.map (tparam_of z g) ps in
    let ts2 = tys_of z g ts in
    ck_modifiers z is_class_modifier ms2;

    (* BSS: 4.1.2 *)
    check (L.all (fun t -> G.kind g (G.name_of z g (P.ty_name t)) = Ciface) ts)
      "%s: some implementation type is not an interface" z;
    check (L.is_uniq ts) "%s: interfaces are not unique" z;
    (* BSS: 4.1.2: check if implicitly abstract? *)
    (* BSS: 4.1.3: TODO acyclic inheritance *)
    (* BSS: 4.1.4: TODO package and accessibility *)

    let g2 = G.enter_class g x in
    let bs2 = L.map (body_of g2) bs in
    Iface (z, ms2, G.this g, ps2, ts2, bs2)

  | P.Annot (z,ms,x,bs) -> 
    let ms2 = modifiers_of g ms in
    ck_modifiers z is_class_modifier ms2;
    let g2 = G.enter_class g x in
    let bs2 = L.map (body_of g2) bs in
    Annot (z, ms2, G.this g2, bs2)

  | P.Enum (z,ms,x,_,_,bs) -> 
warn "TODO: enum not type-checked properly yet";
    let ms2 = modifiers_of g ms in
    ck_modifiers z is_class_modifier ms2;
    let g2 = G.enter_class g x in
    let bs2 = L.map (body_of g2) bs in
    Enum (z, ms2, G.this g2, [], [], bs2) (* TODO *)

and signat_of (z:info) (g:G.t) ((fs,fo,eo,ns):P.signat) : signat =
  (L.map (formal_of z g) fs, opt_map (formal_of z g) fo, opt_map (exp_of g) eo, 
   L.map (G.name_of z g) ns)

and body_of (g:G.t) : P.body -> body = function
  | P.Field (z,ms,t,x) ->              (* JLS 8.3 *)
    let ms2 = modifiers_of g ms in
    ck_modifiers z is_field_modifier ms2;    
    Field (z, ms2, ty_of z g t, G.this g, x)

  | P.Ctor (z,ms,ps,x,s,b) ->
    let ms2 = modifiers_of g ms in
    ck_modifiers z is_ctor_modifier ms2;
    let ps2 = L.map (tparam_of z g) ps in
    let (fs2,fo2,eo2,ns2) as s2 = signat_of z g s in
    let fs3 = fs2 @ (vararg_of fo2) in
    ck_formals z fs3;
    let g2 = L.foldl (fun g0 (_,t,x) -> G.add g0 x t) g fs3 in
    let b2 = code_of z Tvoid g2 b in
    Ctor (z, ms2, ps2, G.this g, x, s2, b2)

  | P.Method (z,ms,ps,t,x,s,bo) ->
    let ms2 = modifiers_of g ms in
    ck_modifiers z is_method_modifier ms2;
    let ps2 = L.map (tparam_of z g) ps in
    let t2 = ty_of z g t in
    
    (* TODO: check override *)
(* FIXME: check it later. allow stub code for dummy classes now to do testing..
 
    check (bo <> None || (L.mem Abstract ms2 || L.mem Native ms2))
      "%s: empty method must have modifier 'abstract' or 'native'" z;
    check (bo = None || not (L.mem Abstract ms2 || L.mem Native ms2))
      "%s: non-empty method must not have modifier 'abstract' or 'native'" z;
*)

    let (fs2,fo2,eo2,ns2) as s2 = signat_of z g s in
    ck_formals z fs2;
    let g1 = L.foldl (fun g0 (_,t,x) -> G.add g0 x t) g fs2 in
    (* variable argument as array *)
    let g2 = match fo2 with None -> g1 | Some (_,t,x) -> G.add g1 x (array_type t 1) in
    let bo2 = opt_map (code_of z t2 g2) bo in
    let k = if is_static ms2 then Istatic else Ivirtual in
    Method (z, ms2, k, ps2, t2, G.this g, x, s2, bo2)

  | P.Init (z,x,b) -> Init (z, x, code_of z Tvoid g b)
  | P.Inner (z,d) -> Inner (z, decl_of (G.enter_inner g) d)
    
and stmt_of (rt:ty) (g:G.t) : P.stmt -> G.t * stmt = function
  | P.Assert (z,e,eo) ->                  (* JLS 14.10 *)
    (g, Assert (z, G.this g, exp_of_ty g e Tbool, opt_map (exp_of g) eo))
  | P.Block (z,b) ->                      (* JLS 14.2 *)
    (g, Block (z, block_of rt g b))
  | P.Break (z,xo) -> (g, Break (z,xo)) (* JLS 14.15 *)
  | P.Continue (z,xo) -> (g, Continue (z,xo))
  | P.Default z -> (g, Default z)
  | P.Do (z,s,e) ->                       (* JLS 14.13 *)
    (g, Do (z, snd (stmt_of rt g s), exp_of_ty g e Tbool))
  | P.Exp (z,e) ->                        (* JLS 14.8 *)
    (g, Exp (z, exp_of g e))
    (* TODO: only Assignment | PreIncrementExpression | PreDecrementExpression 
  | PostIncrementExpression | PostDecrementExpression | MethodInvocation 
  | ClassInstanceCreationExpression ; *)
  | P.ForEach (z,ls,x,e,s) ->
    let e2 = exp_of g e in
    let t2 = exp_ty (exp_of g (P.Ident (z,x))) in
    let (_,_,i) = G.var g x in
    ck_iter z g t2 (exp_ty e2);
    let s2 = snd (stmt_of rt g s) in
    (g, ForEach (z, block_of Tvoid g ls, t2, x, i, e2, s2))
  | P.ForExp (z,e,es,s) ->          (* JLS 14.14.1 *)
    let e2 = exp_of_ty g e Tbool in
    let es2 = exps_of g es in
    let s2 = snd (stmt_of rt g s) in
    (g, ForExp (z,e2,es2,s2))
  | P.If (z,e,s1,s2) ->                    (* JLS 14.7 *)
    let e2 = exp_of_ty g e Tbool in
    let s3 = snd (stmt_of rt g s1) in
    let s4 = snd (stmt_of rt g s2) in
    (g, If (z,e2,s3,s4))
  | P.Label (z,x) -> (g, Label (z,x))   (* JLS 14.7 *)  
  | P.Local (z,d) -> (g, Local (z, decl_of g d))
  | P.Return (z,eo) -> (g, Return (z, expo_of_ty g eo rt))
  | P.Switch (z,e,b) -> 
    let e2 = exp_of_ty g e Tint in
    (g, Switch (z, e2, block_of rt g b))
  | P.Case (z,e) -> (g, Case (z, exp_of_ty g e Tint))
  | P.Sync (z,e,b) -> (g, Sync (z, exp_of g e, block_of rt g b))
  | P.Throw (z,e) -> (g, Throw (z, exp_of g e))
(*  | P.Throw (z,e) -> (g, Throw (z, exp_of_ty g e (Tcname cthrowable))) TODO: rt.jar *)
  | P.Try (z,b1,cs,b2) -> 
    let cs2 = L.map (catch_of z rt g) cs in
    (g, Try (z, block_of rt g b1, cs2, block_of rt g b2))
  | P.Vdecl (z,ms,t0,x) -> 
    let ms2 = modifiers_of g ms in
    ck_modifiers z is_variable_modifier ms2;    
    let t2 = ty_of z g t0 in
    (G.add g x t2, Vdecl (z, ms2, t2, x))
  | P.While (z,e,s) -> 
    (g, While (z, exp_of_ty g e Tbool, snd (stmt_of rt g s)))

and block_of (rt:ty) (g:G.t) (b:P.block) : block = 
  (* lexical scope of blocks: throw away the modified environment *)
  snd (L.map_state (stmt_of rt) g b)

(* add 'return' statement at the end of block, if missing *)
and code_of (z:info) (rt:ty) (g:G.t) (b:P.block) : block =
  let b2 = block_of rt g b in
  if rt<>Tvoid || L.size b2=0 then b2 else      
  match L.last b2 with
  | Return _ -> b2
  | _ -> b2 @ [Return (z, None)]

and catch_of (z:info) (rt:ty) (g:G.t) ((ms,t2,x,b):P.catch) : catch = 
  let ms2 = modifiers_of g ms in
  let b2 = block_of rt (G.add g x (ty_of z g t2)) b in
  (ms2, ty_of z g t2, x, b2)

and exp_of (g:G.t) : P.exp -> exp = function
  | P.Escape (z,e) ->
    let e2 = exp_of g e in
    let t2 = exp_ty e2 in
    printf "%s: Escape: checking g |- [e] = e2 : t where
  g = %s
  e = %s
 e2 = %s
  t = %s\n" z (G.show g) (P.exp_show e) (exp_show e2) (ty_show t2); e2
  | P.Array (z,es) -> 
    let es2 = exps_of g es in
    let t = array_type (join z g (L.map exp_ty es2)) 1 in
    Array (z, t, es2)
  | P.Binary (z,e1,b,e2) -> 
    let e3 = exp_of g e1 in
    let e4 = exp_of g e2 in
    exp_binary_of z g e3 (exp_ty e3) e4 (exp_ty e4) b
  | P.Instof (z,e,t) ->
    let e2 = exp_of g e in
    let t2 = ty_of z g t in
    ck_conv z g (exp_ty e2) t2; Instof (z, e2, t2)
  | P.Cond (z,e1,e2,e3) -> 
    let e4 = exp_of_ty g e1 Tbool in
    let e5 = exp_of g e2 in    
    let e6 = exp_of g e3 in
    let t = join2 z g (exp_ty e5) (exp_ty e6) in
    Cond (z, e4, cast g e5 t, cast g e6 t)
  | P.Cast (z,t,e) -> 
    let e2 = exp_of g e in
    let t2 = exp_ty e2 in
    let t1 = ty_of z g t in
    if subty z g t1 Tdouble && subty z g t2 Tdouble 
    then Cast (z, t1, e2)               (* numeric conversion *)
    else (ck_conv z g t2 t1; Cast (z, t1, e2))
  | P.Pos (z,e) -> exp_of_st g e Tdouble
  | P.Neg (z,e) -> Neg (z, exp_of_st g e Tdouble)
  | P.Inv (z,e) -> Inv (z, exp_of_st g e Tdouble)
  | P.Not (z,e) -> Not (z, exp_of_ty g e Tbool)
  | P.ExpClass (z,t) -> ExpClass (z, ty_of z g t)
  | P.Inst (z, ts, e) -> (* todo *) Std.assert_false ()
  | P.True z -> True z
  | P.False z -> False z
  | P.Null z -> Null z
  | P.This z -> this_of z g
  | P.Super z -> super_of z g
  | P.Char (z,s) -> Char (z,s)
  | P.Int (z,s) -> Int (z,s)
  | P.Long (z,s) -> Long (z,s)
  | P.Float (z,s) -> Float (z,s)
  | P.Double (z,s) -> Double (z,s)
  | P.Str (z,s) -> Str (z,s)
  | P.Offset (z,e1,e2) -> 
    let e3 = exp_of g e1 in
    (match exp_ty e3 with Tarray _ -> () | _ -> error "%s: not an array type" z);
    let e4 = exp_of_ty g e2 Tint in
    Aload (z, e3, e4)
  | P.Ident (z,x) ->
    (try let (t,_,i) = G.var g x in Load (z, t, x, i) (* x *)      
    with Not_found -> 
    try                                 
      let (ms,_,_,_) as fty = G.field g (G.this g) x in
      if is_static ms then Get (z, None, fty) (* f *)
      else Get (z, Some (this_of z g), fty) (* this.f *)
    with Not_found -> error "%s: unbound identifier of form x: %s" z x)
  | P.Dot (z,e,P.This _) ->             (* n.this *)
    let c = exp_cname z g e in Load (z, Tcname c, "this", 0)
  | P.Dot (z,e,P.Ident (_,"length")) ->        (* e.length *)
    let e2 = exp_of g e in Length (z, e2)
  | P.Dot (z,e,P.Dot (_,P.Super _,P.Ident (_,x))) -> (* n.super.x *) 
    let c = exp_cname z g e in
    Get (z, None, G.field g (G.super z g c) x)
  | P.Dot (z,e,P.Ident (_,x)) when is_cname g e -> (* n.x *)    
    (try Get (z, None, G.field g (exp_cname z g e) x)
    with Not_found -> error "%s: unbound field of form n.x for %s: %s" 
      z (cname_show (exp_cname z g e)) x)
  | P.Dot (z,e,P.Ident (_,x)) ->        (* e.x *)
    let e2 = exp_of g e in
    let n = ty_cname (exp_ty e2) in
    (try Get (z, Some e2, G.field g n x)
    with Not_found -> error "%s: unknown field of form e.x: %s" z x)
  | P.Dot (z,_,_) -> error "%s: invalid dot expression" z
  (*- Assign is the same as variable access, field access, and array element access. *)
  | P.Assign (z,p,P.Ident (_,x),a,e) -> (* x = e *)
    let e2 = exp_of g e in
    (try let (t,_,i) = G.var g x in Store (z, p, x, i, a, e2) (* x *)
    with Not_found -> 
    (* TODO: check if the enclosing method is static *)
    try                                 
      let (ms,_,_,_) as fty = G.field g (G.this g) x in
      if is_static ms then Put (z, p, None, fty, a, e2) (* f = e *)
      else Put (z, p, Some (this_of z g), fty, a, e2) (* this.f *)
    with Not_found -> error "%s: unbound field of form x = e: %s" z x)
  | P.Assign (z,p,P.Dot (_,e,P.Dot (_,P.Super _,P.Ident (_,x))),a,e2) -> 
    (* n.super.x = e2 *) 
    let e3 = exp_of g e2 in
    let n = exp_cname z g e in
    Put (z, p, None, G.field g (G.super z g n) x, a, e3)
  | P.Assign (z,p,P.Dot (_,e,P.Ident (_,x)),a,e2) when is_cname g e -> (* n.x = e*)    
    let e3 = exp_of g e2 in
    (try Put (z, p, None, G.field g (exp_cname z g e) x, a, e3)
    with Not_found -> error "%s: unbound field of form n.x = e: %s" z x)
  | P.Assign (z,p,P.Dot (_,e1,P.Ident (_,x)),a,e2) ->        (* e.x *)
    let e3 = exp_of g e1 in
    let e4 = exp_of g e2 in
    let n = ty_cname (exp_ty e3) in
    (try Put (z, p, Some e3, G.field g n x, a, e4)
    with Not_found -> error "%s: unbound field of form e.x = e: %s" z x)
  | P.Assign (z,p,P.Offset (_,e1,e2),a,e3) -> 
    let e4 = exp_of g e1 in
    (match exp_ty e4 with Tarray _ -> () | _ -> error "%s: not an array type" z);
    let e5 = exp_of_ty g e2 Tint in
    let e6 = exp_of g e3 in
    Astore (z, p, e4, e5, a, e6)
  | P.Assign (z,_,_,_,_) -> error "%s: wrong form of assignment" z
(*  -- Forms of method and constructor invocations
    x(es);
    n.x(es);
    e.<ts>x(es);
    n.<ts>x(es);
    super.<ts>x(ts);
    n.super.<ts>x(ts);
    e.<ts>super(es);

    <ts>this(es);
    <ts>super(es);
    e.<ts>super(es);
*)
  | P.Invoke (z,P.Ident (_,x),es) -> (* method: x(ts) *)
    invoke_virtual_of g (this_of z g) x es
  | P.Invoke (z,P.Dot (_,e,P.Ident (_,x)),es) 
    when is_cname g e -> (* method: n.x(ts) *)
    invoke_static_of z g (exp_cname z g e) x es
  | P.Invoke (z,P.Dot (_,P.Dot (_,n,P.Super _),P.Ident (_,x)),es) -> 
    (* method of outer class: n.super.x(ts) *)
    (* todo *) Std.assert_false ()
  | P.Invoke (z,P.Dot (_,e,P.Ident (_,x)),es) -> (* method: e.x(ts) *)
    invoke_virtual_of g (exp_of g e) x es
  | P.Invoke (z,P.This _,es) ->                  (* ctor: this(es) *)
    let es2 = exps_of g es in
    let tys2 = L.map exp_ty es2 in
    let mty = ctor_resolve z g (G.this g) tys2 in
    Invoke (z, None, mty, es2)
  | P.Invoke (z,P.Super _,es) ->                  (* ctor: super(es) *)
    let es2 = exps_of g es in
    let tys2 = L.map exp_ty es2 in
    let mty = ctor_resolve z g (G.super z g (G.this g)) tys2 in
    Invoke (z, Some (this_of z g), mty, es2)
  | P.Invoke (z,P.Dot (_,e,P.Super _),es) ->         (* ctor: e.super(es) *)
    (* todo *) Std.assert_false ()
  | P.Invoke (z,_,_) as e -> 
    error "%s: Invalid form of constructor or method invocation" z (P.exp_show e)
  | P.NewArrNone (z,t,es,i) -> 
    let es2 = L.map (fun e -> exp_of_ty g e Tint) es in
    let t0 = ty_of z g t in
    let t1 = array_type t0 (L.size es + i) in (* type of array itself *)
    NewArrNone (z, t1, es2, i)
  | P.NewArrSome (z,t,es) -> 
    let t0 = ty_of z g t in
    let t2 = array_base t0 in           (* type of array element *)
    let es2 = exps_of_ty g es t2 in
    NewArrSome (z, t0, es2)
  | P.NewObj (z,n,ws,es,bs) ->
    let es2 = exps_of g es in
    let mty = ctor_resolve z g (G.name_of z g n) (L.map exp_ty es2) in
    NewObj (z, mty, es2, [])            (* TODO: check bs *)

and this_of (z:info) (g:G.t) : exp = 
  Load (z, Tcname (G.this g), "this", 0)

and super_of (z:info) (g:G.t) : exp = 
  Load (z, Tcname (G.super z g (G.this g)), "this", 0)

and exps_of (g:G.t) (es:P.exps) : exps = 
  L.map (exp_of g) es

(*-- Check and cast e to have the expected type 't'. *)

and exps_of_ty (g:G.t) (es:P.exps) (t:ty) : exps =
  L.map (fun e -> exp_of_ty g e t) es

and expo_of_ty (g:G.t) (eo:P.expo) (t:ty) : expo =
  opt_map (fun e -> exp_of_ty g e t) eo

and exp_of_ty (g:G.t) (e:P.exp) (t:ty) : exp =
  let e2 = exp_of g e in
  ck_st g e2 t;
  cast g e2 t

(* Check (without casting) e to have the expected type 't'. *)
and exp_of_st (g:G.t) (e:P.exp) (t:ty) : exp =
  let e2 = exp_of g e in
  ck_st g e2 t; e2

and exp_binary_of (z:info) (g:G.t) (e1:exp) (t1:ty) (e2:exp) (t2:ty) 
  : P.binary -> exp = function
      (* FIXME: check if small characters *)
  | P.Add when (t1=Tchar && t2=Tint) || (t2=Tchar && t1=Tint) ->
    Binary (z, Tchar, e1, P.Add, e2)
  | P.Add when is_stringable t1 || is_stringable t2 -> (* promote to string *)
    Binary (z, tstring, cast g e1 tstring, P.Add, cast g e2 tstring)
  | P.Add ->
    ck_st g e1 Tdouble;
    ck_st g e2 Tdouble;
    let t = join z g [t1; t2; Tint] in
    Binary (z, t, cast g e1 t, P.Add, cast g e2 t)
  | P.Eq | P.Ne as b ->
    ck_conv z g t1 t2;
    let t = join z g [t1; t2] in
    Binary (z, Tbool, cast g e1 t, b, cast g e2 t)
  | P.Lt | P.Gt | P.Le | P.Ge as b ->
    ck_st g e1 Tdouble;
    ck_st g e2 Tdouble; 
    let t = join z g [t1; t2] in
    Binary (z, Tbool, cast g e1 t, b, cast g e2 t)
  | P.Sub | P.Mul | P.Div | P.Rem as b ->
    ck_st g e1 Tdouble;
    ck_st g e2 Tdouble;
    let t = join z g [t1; t2; Tint] in
    Binary (z, t, cast g e1 t, b, cast g e2 t)
  | P.Or | P.Xor | P.And as b when subty z g t1 Tbool && subty z g t2 Tbool ->
    Binary (z, Tbool, cast g e1 Tbool, b, cast g e2 Tbool)
  | P.Or | P.Xor | P.And as b ->
    ck_st g e1 Tlong; 
    ck_st g e2 Tlong;
    let t = join z g [t1; t2; Tint] in
    Binary (z, t, cast g e1 t, b, cast g e2 t)
  | P.Shl | P.Shr | P.Ushr as b -> 
    ck_st g e1 Tlong; 
    ck_st g e2 Tlong;
    let t = join z g [t1; t2; Tint] in
    Binary (z, t, cast g e1 t, b, cast g e2 t)

and invoke_virtual_of (g:G.t) (e:exp) (x:id) (es:P.exps) : exp =
  let z = exp_info e in
  let c = ty_cname (exp_ty e) in
  let es2 = exps_of g es in
  let ts = L.map exp_ty es2 in
  let mty = method_resolve z g c x ts in
  Invoke (z, Some e, mty, es2)

and invoke_static_of (z:info) (g:G.t) (c:cname) (x:id) (es:P.exps) : exp =
  let es2 = exps_of g es in
  let ts = L.map exp_ty es2 in
  let mty = method_resolve z g c x ts in
  Invoke (z, None, mty, es2)

and exp_name : P.exp -> P.name = function
  | P.Dot (_,e,P.Ident (_,x)) -> exp_name e @ [x]
  | P.Ident (_,x) -> [x]
  | _ -> raise Fail

and exp_cname (z:info) (g:G.t) (e:P.exp) : cname =
  G.name_of z g (exp_name e)

and is_cname (g:G.t) (e:P.exp) : bool =
  try ignore (G.cname_of g (exp_name e)); true
  with Fail -> false
  | Not_found -> false
