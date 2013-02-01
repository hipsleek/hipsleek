(* jasm.ml - java assembly *)

open Std
module P = Jplain
module T = Jtyped
module L = Listx
module S = Strx


(* flow:

0. linearize expressions and statements into opcodes
1. resolution of labels
2. numeric comparison to branches

*)


type cfile = {                           (* class file 4.1 *)
  src : string;
  kind : T.ckind;
  flags : flags;
  this : cname;
  super : cname;
  ifaces : cname list;
  fields : finfo list;
  methods : minfo list;
  attrs : attrs;
}

and ty =                                (* field type 4.3.2 *)
  | Tarray of ty
  | Tref of cname
  | Tbool
  | Tbyte
  | Tchar
  | Tdouble
  | Tfloat
  | Tint
  | Tlong
  | Tshort
  | Tvoid

and cname = T.cname                        (* class info 4.4.1 *)
and id = utf8                            (* simple name 4.4.6 *)
and utf8 = string                       (* utf-8 4.4.7 *)

and mty = flags * T.ikind * ty * cname * id * ty list (* method type *)
and fty = flags * ty * cname * id   (* field type *)

and finfo = fty * attrs                 (* field info 4.5 *)
and minfo = mty * attrs                 (* method info 4.6 *)

and attr =                              (* attrs 4.7 *)
  | Acode of acode

and attrs = attr list

and handler = label * label * label * cname (* exception handler *)

(* max stack, max locals, code, exceptions *)
and acode = int * int * ops * handler list (* code attribute 4.7.4 *)

(* Datatype copying unsupported in F# *)
(*
and ikind = T.ikind =                     (* function ikind *)
  | Iiface                              (* interface *)
  | Ispecial                            (* constructor *)
  | Ivirtual                            (* virtual / instance *)
  | Istatic                             (* static *)
*)

and flag =                              (* flags flag *)
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

and flags = flag list


(*--- Operand Code. *)

and label = string

and op =
  | Nop                                (* no operation *)

  | Char of string                      (* push char *)
  | Int of int32                        (* push int *)
  | Long of int64                       (* push long *)
  | Float of float                      (* push float *)
  | Double of float                     (* push double *)
  | Str of string                       (* push string *)
  | Class of string                       (* push class *)
  | Null                                (* push null reference *)
  | Load of ty * int                    (* load variable *)
  | Store of ty * int                   (* store variable *)
  | Aload of ty                         (* load array *)
  | Astore of ty                        (* store array *)

  | Dup of int * int                    (* duplicate: size and offset *)
  | Pop of int                          (* pop *)
  | Swap                                (* swap *)

  | Add of ty                            (* add *)
  | Sub of ty                            (* subtract *)
  | Mul of ty                            (* multiple *)
  | Div of ty                            (* divide *)
  | Rem of ty                            (* remainder *)
  | Neg of ty                            (* negate *)
  | Shl of ty                            (* shift left *)
  | Shr of ty                            (* shift right *)
  | Ushr of ty                           (* unsigned shift right *)
  | And of ty                            (* bitwise and *)
  | Or of ty                             (* bitwise or *)
  | Xor of ty                                 (* bitwise xor *)
  | Inc of ty * int * int                           (* increment *)


  | Cmp of ty * cmp                     (* comparison operation *)
  | Conv of ty * ty                     (* conversion *)

  | Ifeq of label                                 (* if zero *)
  | Ifne of label                                 (* if nonzero *)
  | Goto of label                      (* goto *)
  | Label of label                     (* label *)

  | Jsr                                 (* jump subroutine *)
  | Ret                                 (* return from subroutine *)
  | Switch                              (* lookup switch *)
  | Return of ty option                 (* return *)
  | Get of fty                          (* get field *)
  | Put of fty                          (* put field *)
  | Invoke of mty                       (* invoke *)
  | New of ty                           (* new *)
  | Arraylength                         (* array length *)
  | Athrow                              (* throw exception *)
  | Instanceof of cname                 (* instance of *)
  | Monitorenter                        (* enter monitor *)
  | Monitorexit                         (* exit monitor *)

and cmp =
  | Eq
  | Ne
  | Lt
  | Ge
  | Gt
  | Le

and ops = op list


(*---- Show as strings. *)

let cmp_show = function
  | Eq -> "eq"
  | Ne -> "ne"
  | Lt -> "lt"
  | Ge -> "ge"
  | Gt -> "gt"
  | Le -> "le"

let rec ty_show = function
  | Tarray t -> "[" ^ ty_show t
  | Tref c -> "L" ^ cname_show c ^ ";"
  | Tbool -> "Z"
  | Tbyte -> "B"
  | Tchar -> "C"
  | Tdouble -> "D"
  | Tfloat -> "F"
  | Tint -> "I"
  | Tlong -> "J"
  | Tshort -> "S"
  | Tvoid -> "V"

and cname_show = T.cname_show

and attr_show = function
  | Acode (ns,nx,os,hs) -> 
    showf "Code attribute: max_stack=%d, max_locals=%d,\n%s\n"
      ns nx (ops_show os)

and attrs_show (az:attrs) : string = L.show1 attr_show az

and cfile_show (c:cfile) : string = 
  showf "Class file for %s (%s): %s %s extends %s implements [%s]\n%s\n%s\n" 
    c.src (T.ckind_show c.kind) (flags_show c.flags) 
    (cname_show c.this) (cname_show c.super)
    (L.show ", " cname_show c.ifaces) 
    (L.show1 finfo_show c.fields)
    (L.show1 minfo_show c.methods)

and finfo_show ((t,az):finfo) : string =
  showf "Field: %s\n%s" (fty_show t) (attrs_show az)

and minfo_show ((t,az):minfo) : string =
  showf "Method: %s\n%s" (mty_show t) (attrs_show az)

and flag_show = function
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

and flags_show fs = L.showz flag_show fs

and mty_show ((fs,k,t,n,x,ts):mty) : string =
  showf "%s[%s] %s %s.%s(%s)" (flags_show fs)
    (T.ikind_show k) (ty_show t) (cname_show n) x
    (L.show "," ty_show ts)

and fty_show ((fs,t,n,x):fty) : string = 
  showf "(%s%s,%s,%s)" (flags_show fs)
    (ty_show t) (cname_show n) x

and op_show : op -> string = function
  | Nop -> "noop"
  | Char s -> "char " ^ s
  | Int s -> "int " ^ (int32_show s)
  | Long s -> "long " ^ (int64_show s)
  | Float s -> "float " ^ (float_show s)
  | Double s -> "double " ^ (float_show s)
  | Str s -> "str " ^ S.code s                 
  | Class s -> "class " ^ s                 
  | Null -> "null"
  | Load (t,i) -> showf "load %s %d" (ty_show t) i
  | Store (t,i) -> showf "store %s %d" (ty_show t) i
  | Aload t -> showf "aload %s" (ty_show t)
  | Astore t -> showf "astore %s" (ty_show t)
  | Dup (i1,i2) -> showf "dup %d %d" i1 i2
  | Pop i -> showf "pop %d" i
  | Swap -> "swap"

  | Add t -> showf "add %s" (ty_show t)
  | Sub t -> showf "sub %s" (ty_show t)
  | Mul t -> showf "mul %s" (ty_show t)
  | Div t -> showf "div %s" (ty_show t)
  | Rem t -> showf "rem %s" (ty_show t)
  | Neg t -> showf "neg %s" (ty_show t)
  | Shl t -> showf "shl %s" (ty_show t)
  | Shr t -> showf "shr %s" (ty_show t)
  | Ushr t -> showf "ushr %s" (ty_show t)
  | And t -> showf "and %s" (ty_show t)
  | Or t ->showf  "or %s" (ty_show t)
  | Xor t -> showf "xor %s" (ty_show t)
  | Inc (t,i,j) -> showf "inc %s %d %d" (ty_show t) i j


  | Cmp (t,a) -> showf "cmp %s %s" (ty_show t) (cmp_show a)
  | Conv (t1,t2) -> showf "conv %s %s" (ty_show t1) (ty_show t2)
  | Ifeq l -> "ifeq " ^ l
  | Ifne l -> "ifne " ^ l
  | Goto l -> "goto " ^ l
  | Label l-> "label " ^ l
  | Jsr -> "jsr"
  | Ret -> "ret"
  | Switch -> "switch"
  | Return None -> "return"
  | Return (Some t) -> "return " ^ (ty_show t)
  | Get f -> "get " ^ (fty_show f)
  | Put f -> "put " ^ (fty_show f)
  | Invoke f -> "invoke " ^ (mty_show f)
  | New t -> "new " ^ (ty_show t)
  | Arraylength -> "arraylength"
  | Athrow -> "athrow"
  | Instanceof _ -> "instanceof"
  | Monitorenter -> "monitorenter"
  | Monitorexit -> "monitorexit"

and ops_show (os:ops) : string = L.show1 op_show os


(*---- Translate *)

type info = T.info

let tclass = Tref T.cclass

let new_label : string -> string =
  let counter = ref 0 in
  (fun (x:string) -> incr counter; "#" ^ x ^ "_" ^ int_show !counter)

let rec ty_of : T.ty -> ty = function
  | T.Tarray (t,0) -> ty_of t
  | T.Tarray (t,i) -> assert (i>0); Tarray (ty_of (T.Tarray (t,i-1)))
  | T.Tinst (t,_) -> ty_of t
  | T.Tcname n -> Tref n
  | T.Tvar (x,_) -> Tref ([],[],x)      (* FIXME: generic *)
  (* FIXME: T.Tbottom should not be exposed outside Typed, 
  but some places that have literal 'null' because their types do not matter, 
  and then T.Tbottom shows up as a result from the function 'T.ty_exp' *)
  | T.Tbottom -> (* todo *) assert_false ()
  | T.Tnull -> ty_of T.tobject
  | T.Tbool -> Tbool
  | T.Tbyte -> Tbyte
  | T.Tchar -> Tchar
  | T.Tdouble -> Tdouble
  | T.Tfloat -> Tfloat
  | T.Tint -> Tint
  | T.Tlong -> Tlong
  | T.Tshort -> Tshort
  | T.Tvoid -> Tvoid

(* invalid label, never occurs in program unless the 'enclosing
invariant' in jtyped.ml is violated: a break or continue statement
occurs outside 'switch', 'for', 'while', or 'do' statements. *)
let invalid = "_invalid"

let rec ctask_of (t:T.ctask) : cfile list =
  L.mapc cunit_of t

and cunit_of ((_,_,ds):T.cunit) : cfile list =
  L.mapc decl_of ds

and decl_of : T.decl -> cfile list = function
  | T.Class (z,ms,c,ps,t,ts,bs) -> 
    { src = Util.info_filename z;
      kind = T.Cclass;
      flags = modifiers_of ms;
      this = c;
      super = T.ty_cname t;
      ifaces = L.map T.ty_cname ts;
      fields = L.collect field_of bs;
      methods = L.collect method_of bs;
      attrs = [];
    } :: L.mapc inner_of bs
  | T.Iface (z,ms,c,ps,ts,bs) -> 
    { src = Util.info_filename z;
      kind = T.Ciface;
      flags = modifiers_of ms;
      this = c;
      super = T.ty_cname T.tobject;
      ifaces = L.map T.ty_cname ts;
      fields = L.collect field_of bs;
      methods = L.collect method_of bs;
      attrs = [];
    } :: L.mapc inner_of bs
  | T.Enum (z,ms,c,ts,es,bs) ->
    { src = Util.info_filename z;
      kind = T.Ciface;
      flags = modifiers_of ms;
      this = c;
      super = T.ty_cname T.tobject;
      ifaces = L.map T.ty_cname ts;
      fields = L.collect field_of bs;
      methods = L.collect method_of bs;
      attrs = [];
    } :: L.mapc inner_of bs
  | T.Annot (z,ms,c,bs) ->
    { src = Util.info_filename z;
      kind = T.Ciface;
      flags = modifiers_of ms;
      this = c;
      super = T.ty_cname T.tobject;
      ifaces = [];
      fields = L.collect field_of bs;
      methods = L.collect method_of bs;
      attrs = [];
    } :: L.mapc inner_of bs

and field_of : T.body -> finfo option = function
  | T.Field (_,ms,t,c,x) -> Some ((modifiers_of ms, ty_of t, c, x), [])
  | _ -> None

and inner_of : T.body -> cfile list = function
  | T.Inner (_,d) -> decl_of d
  | _ -> []

and method_of : T.body -> minfo option = function
  | T.Method (_,ms,k,ps,t,c,x,s,bo) ->
    let ops = opt_list (opt_map (block_of invalid invalid) bo) in
    let attr = Acode (999, 999, ops, []) in (* TODO TODO: max_locals *)
    Some ((modifiers_of ms, k, ty_of t, c, x, signat_of s), [attr])
  | T.Ctor (z,ms,ps,c,x,s,b) ->
    let ops = block_of invalid invalid b in
    let attr = Acode (999, 999, ops, []) in
    Some ((modifiers_of ms, T.Ispecial, Tvoid, c, "<init>", signat_of s), [attr])
  | T.Field _ -> None
  | T.Init (z,s,b) -> None                (* FIXME: put it in constructor *)
  | T.Inner _ -> None

and block_of (lbreak:label) (lcontinue:label) (b:T.block) : ops =
  L.mapc (stmt_of lbreak lcontinue)  b

(* lcontinue: continue label inserted before loop statements for 'continue'
   lbreak: break label inserted after switch or loop statements for 'break' *)
and stmt_of (lbreak:label) (lcontinue:label) : T.stmt -> ops = function 
  | T.Exp (_,e) -> exp_of e @ [Pop (size e)]
  | T.Block (_,b) -> block_of lbreak lcontinue b
  | T.If (z,e,s1,s2) ->
    let lfalse = new_label ("false-" ^ z) in
    let lend = new_label ("end-" ^ z) in
    exp_of e @ Ifne lfalse ::
    stmt_of lbreak lcontinue s1 @ Goto lend ::
    Label lfalse :: stmt_of lbreak lcontinue s2 @
    [Label lend]
  | T.While (z,e,s) ->
    let lbreak = new_label ("break-" ^ z) in
    let lcontinue = new_label ("continue-" ^ z) in
    Label lcontinue :: exp_of e @ Ifne lbreak
    :: stmt_of lbreak lcontinue s @ [Label lbreak]
  | T.Label (_,l) -> [Label l]
  | T.Continue (_,None) -> [Goto lcontinue]
  | T.Continue (_,Some l) -> [Goto l]
  | T.Break (_,None) -> [Goto lbreak]
  | T.Break (_,Some l) -> [Goto l]
  | T.Assert (z,n,e,None) -> 
    (* assert e  == if (n.class.desiredAssertionStatus() ? !e : false) 
         throw new AssertionError() *)
    let e3 = T.Cond (z, assert_of z n, T.Not (z, e), T.False z) in
    let mty = ([], T.Ispecial, T.Tvoid, T.cassertion, "<init>", []) in
    let s = T.Throw (z, T.NewObj (z, mty, [], [])) in
    stmt_of lbreak lcontinue (T.If (z, e3, s, T.Block (z,[])))
  | T.Assert (z,n,e1,Some e2) ->
    (* assert e  ==  if (n.class.desiredAssertionStatus() ? !e : false) 
         throw new AssertionError(e2) *)
    let e3 = T.Cond (z, assert_of z n, T.Not (z, e1), T.False z) in
    let mty = ([], T.Ispecial, T.Tvoid, T.cassertion, "<init>", [T.exp_ty e2]) in
    let s = T.Throw (z, T.NewObj (z, mty, [e2], [])) in
    stmt_of lbreak lcontinue (T.If (z, e3, s, T.Block (z,[])))
  | T.Case _ -> assert_false ()
  | T.Default _ -> assert_false ()
  | T.Do (z,s,e) -> 
    let lbreak = new_label ("break-" ^ z) in
    let lcontinue = new_label ("continue-" ^ z) in
    Label lcontinue :: stmt_of lbreak lcontinue s 
    @ exp_of e @ [Ifeq lcontinue; Label lbreak]
  | T.ForEach (z,ls,T.Tcname t,x,j,e,s) -> (* JLS 14.14.2 *)
    (* l1: .. ln: for (x : e) s  ==  { I i = e.iterator(); l1: .. ln: 
         for (; i.hasNext();) { x = i.next(); s }}   fresh i *)    
    let _ = T.Load (z, T.Tint, "#i", 0) in (* fresh variable i *)
    (* InterfaceMethod java/lang/Iterable.iterator:()Ljava/util/Iterator; *)
    let mty1 = ([], T.Iiface, T.titerator, T.citerable, "iterator", []) in
    let e1 = T.Invoke (z, Some e, mty1, []) in (* e.iterator() *)
    (* i = e.iterator() *)
    let s1 = T.Exp (z, T.Store (z, true, "#i", 0, P.Set, e1)) in 
    let mty2 = ([], T.Iiface, T.Tbool, T.citerable, "hasNext", []) in
    let e2 = T.Invoke (z, Some e, mty2, []) in (* i.hasNext() *)
    let mty3 = ([], T.Iiface, T.tobject, T.citerable, "next", []) in
    let e3 = T.Invoke (z, Some e, mty3, []) in (* i.next() *)
    let s2 = T.Exp (z, T.Store (z, true, x, j, P.Set, e3)) in (* x = i.next() *)
    let s3 = T.ForExp (z, e2, [], T.Block (z, [s2; s])) in (* for ... *)
    stmt_of lbreak lcontinue (T.Block (z, s1 :: ls @ [s3]))

  | T.ForEach (z,ls,t,x,j,e,s) ->       (* JLS 14.14.2 *)
    (* l1: .. ln: for (x : e) s  ==  { t[] a = e; i = 0; l1: .. ln: 
         for (; i < a.length; i++) { x = a[i]; s }}  fresh a, i *)
    let a = T.Load (z, T.array_type t 1, "#a", 1) in (* fresh variable a *)
    let i = T.Load (z, T.Tint, "#i", 0) in (* fresh variable i *)
    let s1 = T.Exp (z, T.Store (z, true, "#a", 1, P.Set, e)) in (* a = e *)
    let s2 = T.Exp (z, T.Store (z, true, "#i", 0,
      P.Set, T.Int (z, 0l))) in     (* i = 0 *)
    let e1 = T.Binary (z, T.Tbool, i, P.Lt, T.Length (z, a)) in (* i < a.length *)
    let e2 = T.Store (z, false, "#i", 0, P.AddSet, T.Int (z, 1l)) in (* i++ *)
    let s3 = T.Exp (z, T.Store (z, true, x, j, 
      P.Set, T.Aload (z, a, i))) in      (* x = a[i] *)    
    let s4 = T.ForExp (z, e1, [e2], T.Block (z, [s3;s])) in (* for ... *)
    stmt_of lbreak lcontinue (T.Block (z, s1 :: s2 :: ls @ [s4]))

  | T.ForExp (z,e,es,s) -> 
    let lbreak2 = new_label ("break-" ^ z) in
    let lcontinue2 = new_label ("continue-" ^ z) in
    Label lcontinue2 :: exp_of e @ Ifne lbreak2 :: stmt_of lbreak2 lcontinue2 s 
    @ exps_of es @ [Goto lcontinue2; Label lbreak2]

  | T.Local _ -> (* todo *) assert_false ()
  | T.Return (_,None) -> [Return None]
  | T.Return (_,Some e) -> exp_of e @ [Return (Some (ty_exp_of e))]
  | T.Switch (z,e,b) -> 
    let lbreak2 = new_label ("break-" ^ z) in
    ignore lbreak2;
    exp_of e @ Switch :: []             (* TODO: case and default *)
(*    block_of lbreak2 lcontinue b *)

  | T.Sync (_,e,b) ->                   (* TODO: exception *)
    exp_of e @ Dup (1,0) :: Monitorenter :: 
    block_of lbreak lcontinue b @
    [Monitorexit]
  | T.Throw (_,e) -> exp_of e @ [Athrow]
  | T.Try (z,b1,cs,b2) ->               (* TODO setup exception table *)
    let lend = new_label ("end-" ^ z) in
    let bfinally = block_of lbreak lcontinue b2 in
    let prolog = bfinally @ [Goto lend] in
    block_of lbreak lcontinue b1 @
    L.mapc (catch_of lbreak lcontinue prolog) cs @ bfinally @ [Label lend]
  | T.Vdecl _ -> []

and catch_of (lbreak:label) (lcontinue:label) (prolog:ops)
  ((_,_,_,b):T.catch) : ops = 
  block_of lbreak lcontinue b @ prolog

and exp_of : T.exp -> ops = function
  | T.True _ -> [Int 1l]
  | T.False _ -> [Int 0l]
  | T.Null _ -> [Null]
  | T.Char (_,x) -> [Char x]
  | T.Int (_,x) -> [Int x]
  | T.Long (_,x) -> [Long x]
  | T.Float (_,x) -> [Float x]
  | T.Double (_,x) -> [Double x]
  | T.Str (_,x) -> [Str x]
  | T.Cond (z,e,e1,e2) ->
    let lfalse = new_label ("false-" ^ z) in
    let lend = new_label ("end-" ^ z) in
    exp_of e @ Ifne lfalse ::
    exp_of e1 @ Goto lend ::
    Label lfalse :: exp_of e2 @
    [Label lend]
  | T.NewObj (z,((_,_,_,n,_,_) as t),es,_) -> 
    New (Tref n) :: Dup (1,0) :: exps_of es @ [Invoke (mty_of t)]
  | T.Instof (_,e,t) -> exp_of e @ [Instanceof (T.ty_cname t)]
  | T.Cast (z,t,e) -> exp_of e @ [Conv (ty_exp_of e, ty_of t)]

  | T.Put (z,true,e1,((_,t,_,_) as f),a,e2) ->         
    (* [[ e1.f op= e2 ]] = [[e1]], dup, get f, [[e2]], op, dup, put f *)
    let get = if a=P.Set then [] else [Get (fty_of f)] in
    opt_map_list exp_of e1 @ Dup (1, 0) :: get @ exp_of e2 
    @ assign_of (ty_of t) a @ [Dup (1,0); Put (fty_of f)]

  | T.Put (z,false,e1,((_,t,_,_) as f),a,e2) ->
    (* [[ e1.f =op e2 ]] = [[e1]], dup, get f, dup, [[e2]], op, dup?_x1, put f *)
    let get = if a=P.Set then [] else [Get (fty_of f)] in
    opt_map_list exp_of e1 @ Dup (1, 0) :: get @ Dup (size e2, 1)
    :: exp_of e2 @ assign_of (ty_of t) a @ [Put (fty_of f)]

  | T.Store (_,true,x,i,a,e) -> 
    (* [[ x op= e ]] = load, [[e]], op, dup, store *)
    let t = ty_exp_of e in
    let load = if a=P.Set then [] else [Load (t, i)] in
    load @ exp_of e @ assign_of t a 
    @ [Dup (size e, 0); Store (ty_exp_of e, i)]

  | T.Store (_,false,x,i,a,e) -> 
    (* [[ x =op e ]] = load, dup, [[e]], op, store *)
    let t = ty_exp_of e in
    let load = if a=P.Set then [] else [Load (t, i)] in
    load @ Dup (size e, 0) :: exp_of e @ assign_of t a @ [Store (ty_exp_of e, i)]

  | T.Astore (_,true,e1,e2,a,e3) -> 
    (* [[ e1[e2] op= e3 ]] = [[e1]] [[e2]] dup2 aload [[e3]] op dup_x2 astore *)
    exp_of e1 @ exp_of e2 @ Dup (2,0) :: Aload (ty_exp_of e3)
    :: exp_of e3 @ assign_of (ty_exp_of e3) a 
    @ Dup (size e3, 2) :: [Astore (ty_exp_of e3)]

  | T.Astore (_,false,e1,e2,a,e3) ->
    (* [[ e1[e2] =op e3 ]] = [[e1]] [[e2]] dup2 aload dup_x2 [[e3]] op astore *)
    exp_of e1 @ exp_of e2 @ Dup (2,0) :: Aload (ty_exp_of e3) :: Dup (size e3, 2) 
    :: exp_of e3 @ assign_of (ty_exp_of e3) a @ [Astore (ty_exp_of e3)]

  | T.Array (_,t,es) -> 
    let f (e,i) = Dup (1,0) :: Int (int32_of i) :: exp_of e @ [Astore (ty_exp_of e)] in
    Int (int32_of (L.size es)) :: New (ty_of t) :: L.cat (L.mapi f es)
  | T.Binary (z,t,e1,b,e2) -> 
    exp_of e1 @ exp_of e2 @
    binary_of (ty_exp_of e1) b
  | T.Neg (_,e) -> exp_of e @ [Neg (ty_exp_of e)]
  | T.Not (_,e) -> exp_of e @ [Int 1l; Xor Tint]
  | T.Inv (_,e) -> exp_of e @ [Int (-1l); Xor Tint]
  | T.Aload (_,e1,e2) as e -> exp_of e1 @ exp_of e2 @ [Aload (ty_exp_of e)]
  | T.ExpClass (_,T.Tint) -> 
    [Get ([], tclass, T.cinteger, "TYPE")]
  | T.ExpClass (_,T.Tbyte) -> 
    [Get ([], tclass, T.cbyte, "TYPE")]
  | T.ExpClass (_,T.Tchar) -> 
    [Get ([], tclass, T.ccharacter, "TYPE")]
  | T.ExpClass (_,T.Tshort) -> 
    [Get ([], tclass, T.cshort, "TYPE")]
  | T.ExpClass (_,T.Tlong) -> 
    [Get ([], tclass, T.clong, "TYPE")]
  | T.ExpClass (_,T.Tdouble) -> 
    [Get ([], tclass, T.cdouble, "TYPE")]
  | T.ExpClass (_,T.Tvoid) -> 
    [Get ([], tclass, T.cvoid, "TYPE")]
  | T.ExpClass (_,T.Tbool) -> 
    [Get ([], tclass, T.cboolean, "TYPE")]
  | T.ExpClass (_,t) -> [Class (ty_show (ty_of t))]
  | T.Load (_,t,_,i) -> [Load (ty_of t, i)]
  | T.NewArrNone (_,t,es,i) -> exps_of es @ [New (ty_of t)]
  | T.NewArrSome (z,t,es) -> exp_of (T.Array (z, t, es)) (* FIXME correct?*)
  | T.Invoke (_,e,t,es) ->
    expo_of e @ L.mapc exp_of es @ [Invoke (mty_of t)]
  | T.Length (_,e) -> exp_of e @ [Arraylength]
  | T.Get (_,e,f) -> 
    opt_map_list exp_of e @ [Get (fty_of f)]

and exps_of (es:T.exps) : ops = L.mapc exp_of es
and expo_of (eo:T.expo) : ops = opt_map_list exp_of eo

and fty_of ((ms,t,n,x):T.fty) : fty = (modifiers_of ms, ty_of t, n, x)

and ty_exp_of (e:T.exp) : ty = ty_of (T.exp_ty e)

and size (e:T.exp) : int = ty_size (ty_of (T.exp_ty e))

and ty_size : ty -> int = function
  | Tarray _ -> 1
  | Tref _ -> 1
  | Tbool -> 1
  | Tbyte -> 1
  | Tchar -> 1
  | Tdouble -> 2
  | Tfloat -> 1
  | Tint -> 1
  | Tlong -> 2
  | Tshort -> 1
  | Tvoid -> 0

and binary_of (t:ty) : P.binary -> ops = function
  | P.Add -> [Add t]
  | P.Sub -> [Sub t]
  | P.Mul -> [Mul t]
  | P.Div -> [Div t]
  | P.Rem -> [Rem t]
  | P.Shl -> [Shl t]
  | P.Shr -> [Shr t]
  | P.Ushr -> [Ushr t]
  | P.And -> [And t]
  | P.Or -> [Or t]
  | P.Xor -> [Xor t]
  | P.Eq -> [Cmp (t, Eq)]
  | P.Ne -> [Cmp (t, Ne)]
  | P.Lt -> [Cmp (t, Lt)]
  | P.Ge -> [Cmp (t, Ge)]
  | P.Gt -> [Cmp (t, Gt)]
  | P.Le -> [Cmp (t, Le)]

and assign_of (t:ty) : P.assign -> ops = function
  | P.Set -> []
  | P.AddSet -> [Add t]
  | P.SubSet -> [Sub t]
  | P.MulSet -> [Mul t]
  | P.DivSet -> [Div t]
  | P.RemSet -> [Rem t]
  | P.ShlSet -> [Shl t]
  | P.ShrSet -> [Shr t]
  | P.UshrSet -> [Ushr t]
  | P.AndSet -> [And t]
  | P.OrSet -> [Or t]
  | P.XorSet -> [Xor t]

and mty_of ((ms,k,t,n,x,ts):T.mty) : mty = 
  (modifiers_of ms, k, ty_of t, n, x, L.map ty_of ts)

(* n.class.desiredAssertionStatus() *)
and assert_of (z:info) (n:T.cname) : T.exp = 
  let mty = ([], T.Ivirtual, T.Tbool, T.cclass, "desiredAssertionStatus", []) in
  T.Invoke (z, Some (T.ExpClass (z, T.Tcname n)), mty, [])

and modifier_of : T.modifier -> flag option = function
  | T.Annotate _ -> None
  | T.Abstract -> Some Abstract 
  | T.Final -> Some Final 
  | T.Native -> Some Native 
  | T.Private -> Some Private 
  | T.Protected -> Some Protected 
  | T.Public -> Some Public 
  | T.Static -> Some Static 
  | T.Strictfp -> Some Strictfp 
  | T.Synchronized -> Some Synchronized 
  | T.Transient -> Some Transient 
  | T.Volatile -> Some Volatile 

and modifiers_of (ms:T.modifiers) : flags = L.collect modifier_of ms

and is_static (fs:flags) : bool = L.mem Static fs

and formal_of (_,t,_) : ty = ty_of t

and signat_of (fs,fo,_,_) = L.map formal_of (fs @ T.vararg_of fo)

