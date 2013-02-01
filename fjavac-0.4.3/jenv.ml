(* jenv.ml - java class definition (from source code) *)

open Std
module H = Hashx
module M = Mapx
module L = Listx
module P = Jplain
module T = Jtyped
module J = Jjar

(* Ways to lookup contextual information (higher shadows lower entries):

- local variables
- fields/methods of current class
- fields/methods of enclosing class
- classes of same file
- classes from .class files
- classes from .jar files

*)

(* Design choices: resolve all names and construct all class types
with all fields and methods types. Compared to the lazy approach in
'Jjar', the eager approach is more optimal because names are not
resolved 'Jplain'. *)

type t = {                              (* binding environment *)
  jar : J.t;                            (* jar files *)
  package : T.package;                  (* package *)
  enclosing : T.id list;                (* enclosing classes *)
  this : T.id;                          (* current class *)
  vmap : (T.id, T.vty) M.t;             (* variables in scope *)
  nmap : (P.name, T.cname) M.t;         (* names in scope *)
  cnames : T.cname list;                (* all class names *)
  ctys : (T.cname, cty) H.t;            (* all class ty *)
}

and cty = {                             (* class type *)
  kind : T.ckind;
  mods : T.modifiers;
  super : T.cname;
  ifaces : T.cname list;
  fields : (T.id, T.fty) H.t;
  methods : (T.id, T.mty list) H.t;
}

exception Unbound of T.info * T.id

let this (g:t) : T.cname = (g.package, g.enclosing, g.this)

let cty_show (t:cty) : string =
  showf "\
(kind : %s
mods : %s
super : %s
ifaces : (%s)
fields : (%s)
methods : (%s))"
    (T.ckind_show t.kind) (T.modifiers_show t.mods)
    (T.cname_show t.super) (L.show1 T.cname_show t.ifaces)
    (H.show1 T.id_show T.fty_show t.fields)
    (H.show1 T.id_show (L.show "; " T.mty_show) t.methods)

let show (g:t) : string = 
  showf "\
(this : %s
vmap : (%s)
nmap : (%s)
cnames : (%s)
ctys : (%s))"
    (T.cname_show (this g))
    (M.show1 T.id_show T.vty_show g.vmap)
    (if 1=0 then (M.show1 P.name_show T.cname_show g.nmap) else "*omitted*")
    (L.show1 T.cname_show g.cnames)
    (H.show2 T.cname_show cty_show g.ctys)


(*---- Class types *)

let object_cty = {                      (* TODO: use rt.jar *)
  kind = T.Cclass;
  mods = [];
  super = T.cobject;
  ifaces = [];
  fields = H.create 1;
  methods = H.create 1;
}

let get (g:t) (c:T.cname) : cty = 
  if T.cname_eq c T.cobject then object_cty (* TODO look up in rt.jar *)
  else H.get g.ctys c

let cname_of (g:t) (n:P.name) : T.cname =
  try M.get n g.nmap 
  with Not_found -> J.cname_of g.jar n

let is_valid (g:t) (c:T.cname) : bool =
  L.mem c g.cnames 
  || (try ignore (J.cname_of g.jar (T.cname_to c)); 
      true with Not_found -> false)

(* All class names (including inner classes) 
   of the package within the enclosing classes. *)
let cnames (g:t) (p:T.package) (cs:T.id list) : T.cname list =
  J.cnames g.jar p cs 
  @ L.take (fun (p2,cs2,_) -> p=p2 && L.is_prefix cs cs2) g.cnames  

(* Method types of a method of a class. *)
let methods (g:t) (c:T.cname) (x:T.id) : T.mty list =
  try H.get (get g c).methods x with Not_found -> []
  @ J.methods g.jar c x

(* Super class of a class. *)
let super (z:T.info) (g:t) (c:T.cname) : T.cname =
  (* FIXME: this check is necessary only because jjar 
is reading type argument of generics. *)
  check (is_valid g c) "%s: %s is not a valid class name (TODO: generics)" 
    z (T.cname_show c);
  try (get g c).super
  with Not_found -> J.super g.jar c

(* Field type of a field of a class. *)
let rec field (g:t) (c:T.cname) (x:T.id) : T.fty =
  if H.mem g.ctys c then 
    try H.get (get g c).fields x
    with Not_found -> field g (get g c).super x
  else J.field g.jar c x

(* Interface classes of a class. *)
let ifaces (g:t) (c:T.cname) : T.cname list = 
  try (get g c).ifaces                  (* FIXME: recursively collect all *)
  with Not_found -> J.ifaces g.jar c

(* Modifiers of a class. *)
let mods (g:t) (c:T.cname) : T.modifiers = 
  try (get g c).mods
  with Not_found -> J.mods g.jar c

(* Kind of a class. *)
let kind (g:t) (c:T.cname) : T.ckind =
  try (get g c).kind
  with Not_found -> J.kind g.jar c



(*-- Computing all class names. *)

type cnames = T.cname list

(* Collect full qualified names: given package 'p' and enclosing classes 'cs'. *)
let rec ctask_cnames (t:P.ctask) : cnames =
  L.mapc cunit_cnames t  

and cunit_cnames ((p,_,ds):P.cunit) : cnames =
  L.mapc (decl_cnames p []) ds

(* name to cname *)
and decl_cnames (p:P.name) (cs:P.id list) : P.decl -> cnames = function
  | P.Class (_,_,x,_,_,_,bs)
  | P.Iface (_,_,x,_,_,bs) 
  | P.Enum (_,_,x,_,_,bs) 
  | P.Annot (_,_,x,bs) ->
    (p, cs, x) :: L.mapc (body_cnames p (x :: cs)) bs

and body_cnames (p:P.name) (cs:P.id list) : P.body -> cnames = function
  | P.Inner (_,d) -> decl_cnames p cs d
  | _ -> []

(*---- Semantics of 'of'. *)

let rec ctask_of (t:P.ctask) : t =
  let cs = ctask_cnames t in
  let g = { 
    jar = J.load "rt.jar";
    package = [];
    enclosing = [];
    this = "_invalid";
    vmap = M.empty; 
    cnames = cs;
    nmap = M.of_list (L.map (fun c -> (T.cname_to c, c)) cs);
    ctys = H.create 2;                  (* to be filled *)
  } in
  L.iter (cunit_of g) t; g

and cunit_of (g:t) ((p,is,ds):P.cunit) : unit =
  let g2 = imports_of (package_of g p) is in
  L.iter (decl_of g2) ds

and package_of (g:t) (p:P.name) : t =
  { (import_all g p []) with package = p }

and imports_of (g:t) (is:P.import list) : t =
  let g2 = import_all g ["java";"lang"] [] in (* default import *)
  L.foldl import_of g2 is

and import_of (g:t) : P.import -> t = function
  | (_,false,n,true) -> import_all g n []
  | (_,false,n,false) -> { g with nmap = M.add [L.last n] (T.cname_of n) g.nmap }
  | _ -> g

and import_all (g:t) (p:T.package) (cs:T.id list) : t =
  let f ((_,cs2,x) as c) = (L.skip (L.size cs) cs2 @ [x], c) in
  { g with nmap = M.list_add g.nmap (L.map f (cnames g p cs)) }

and modifiers_of (ms:P.modifiers) : T.modifiers = 
  L.collect modifier_of ms

and modifier_of : P.modifier -> T.modifier option = function
  | P.Annotate _ -> None
  | P.Abstract -> Some T.Abstract 
  | P.Final -> Some T.Final 
  | P.Native -> Some T.Native 
  | P.Private -> Some T.Private 
  | P.Protected -> Some T.Protected 
  | P.Public -> Some T.Public 
  | P.Static -> Some T.Static 
  | P.Strictfp -> Some T.Strictfp 
  | P.Synchronized -> Some T.Synchronized 
  | P.Transient -> Some T.Transient 
  | P.Volatile -> Some T.Volatile 

and decl_of (g:t) : P.decl -> unit = function
  | P.Class (z,ms,x,ps,t,ts,bs) ->
    let g2 = enter_class g x in
    let c = {
      kind = T.Cclass;
      mods = modifiers_of ms;
      super = name_of z g2 (P.ty_name t);
      ifaces = (L.map (fun t -> name_of z g2 (P.ty_name t)) ts);
      fields = H.of_list (L.collect (field_of g2) bs);
      methods = H.of_list_list (L.collect (method_of g2) bs);
    } in
    L.iter (inner_of g2) bs;
    H.add g2.ctys (this g2) c
  | P.Iface (z,ms,x,ps,ts,bs) ->
    let g2 = enter_class g x in
    let c = {
      kind = T.Ciface;
      mods = modifiers_of ms;
      super = T.cobject;              (* unused *)
      ifaces = L.map (fun t -> name_of z g2 (P.ty_name t)) ts;
      fields = H.of_list (L.collect (field_of g2) bs);
      methods = H.of_list_list (L.collect (method_of g2) bs);
    } in
    L.iter (inner_of g2) bs;
    H.add g2.ctys (this g2) c
  | P.Enum (z,ms,x,ts,es,bs) ->
    let g2 = enter_class g x in
    let c = {
      kind = T.Ciface;
      mods = modifiers_of ms;
      super = T.cobject;              (* unused *)
      ifaces = [];
      fields = H.of_list (L.collect (field_of g2) bs);
      methods = H.of_list_list (L.collect (method_of g2) bs);
    } in
    L.iter (inner_of g2) bs;
    H.add g2.ctys (this g2) c
  | P.Annot (z,ms,x,bs) -> 
    let g2 = enter_class g x in
    let c = {
      kind = T.Cenum;
      mods = modifiers_of ms;
      super = T.cobject;              (* unused *)
      ifaces = [];
      fields = H.of_list (L.collect (field_of g2) bs);
      methods = H.of_list_list (L.collect (method_of g2) bs);
    } in
    L.iter (inner_of g2) bs;
    H.add g2.ctys (this g2) c

and name_of_ty (z:T.info) (g:t) (n:P.name) : T.ty =
  try
    (* FIXME: need this? jjar should have java.lang.Object *)
    if P.name_is_object n then T.tobject 
    else 
      (try T.Tcname (J.cname_of g.jar n)
      with Not_found -> T.Tcname (M.get n g.nmap))
  with Not_found ->
  if L.size n = 1 then (
    (* FIXME: this is only for debugging without generic support *)
    printf "%s: Warning: Treating unbound name '%s' as type variable\n" 
      z (P.name_show n); 
    T.Tvar (L.head n, 0)
   ) else error "%s: Unbound name '%s'" z (P.name_show n)    

and name_of (z:T.info) (g:t) (n:P.name) : T.cname =
  try 
    if P.name_is_object n then T.cobject 
    else 
      (try J.cname_of g.jar n
      with Not_found -> M.get n g.nmap)
  with Not_found ->
    printf "%s: Warning: Treating unbound name '%s' as type name\n" z (P.name_show n); 
    T.cname_of n

and inner_of (g:t) : P.body -> unit = function
  | P.Inner (_,d) -> decl_of (enter_inner g) d
  | _ -> ()

and field_of (g:t) : P.body -> (T.id * T.fty) option = function
  | P.Field (z,ms,t,x) -> 
    Some (x, (modifiers_of ms, ty_of z g t, this g, x))
  | _ -> None

and method_of (g:t) : P.body -> (T.id * T.mty) option = function
  | P.Method (z,ms,ps,t,x,s,_) -> 
    (* FIXME for interface *)
    let k = if T.is_static (modifiers_of ms) then T.Istatic else T.Ivirtual in
    Some (x, (modifiers_of ms, k, ty_of z g t, this g, x, signat_of z g s))
  | P.Ctor (z,ms,ps,x,s,_) ->
    Some ("<init>", (modifiers_of ms, T.Ispecial, T.Tvoid, this g, "<init>", signat_of z g s))
  | _ -> None

and signat_of (z:P.info) (g:t) ((fs,fo,eo,nmap):P.signat) : T.tys =
  L.map (formal_of z g) fs

and formal_of (z:P.info) (g:t) ((ms,t,_):P.formal) : T.ty = ty_of z g t

and ty_of (z:P.info) (g:t) : P.ty -> T.ty = function
  | P.Tarray (t,i) -> T.Tarray (ty_of z g t, i)
  | P.Tinst (t,_) -> T.Tinst (ty_of z g t, []) (* FIXME *)
  | P.Tname n -> T.Tcname (name_of z g n)
  | P.Tbool -> T.Tbool
  | P.Tbyte -> T.Tbyte
  | P.Tchar -> T.Tchar
  | P.Tdouble -> T.Tdouble
  | P.Tfloat -> T.Tfloat
  | P.Tint -> T.Tint
  | P.Tlong -> T.Tlong
  | P.Tshort -> T.Tshort
  | P.Tvoid -> T.Tvoid

and tys_of (z:P.info) (g:t) (ts:P.tys) : T.tys = 
  L.map (ty_of z g) ts

(* enter the scope of a class *)
and enter_class (g:t) (x:T.id) =
  let g2 = import_all g g.package (g.enclosing @ [x]) in
  { g2 with this = x }

(* enter the scope of an inner class *)
and enter_inner (g:t) =
  { g with enclosing = g.enclosing @ [g.this] }


let add (g:t) (x:T.id) (t:T.ty) : t = 
  { g with vmap = M.add x (t, x, M.size g.vmap) g.vmap }

let var (g:t) (x:T.id) : T.vty = M.get x g.vmap

let is_var (g:t) (x:T.id) : bool = M.mem x g.vmap

let is_scope (g:t) (p:T.package) (xs:T.id list) =
  p = ["java"] || p = ["java";"lang"]
