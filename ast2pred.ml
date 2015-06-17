#include "xdebug.cppo"
open VarGen


(*
this module tranform an iast to pred
*)

open Globals
open Gen.Basic
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer

module E = Env
module Err = Error
module I = Iast
module IF = Iformula
module IP = Ipure
module LO = Label_only.LOne
open IastUtil


let has_error_stmt iprog=
  (*func call error*)
  false

(*
  x=y ==> x=y

  if (a) then C_1 else C_2
  a /\ rec(C_1) \/ -a /\ rec(C_2)

*)
let gen_view_from_stmt iprog e0=
  let rec recf e= match e with
    | I.Assign e_ass -> true
    | I.Binary e_bin -> true
    | I.Cond e_cond -> true
    | I.CallRecv _ -> true
    | I.CallNRecv _ -> true
    | I.Empty _ -> true
    | I.FloatLit _ -> true
    | I.IntLit _ -> true
    | I.Null - -> true
    | I.Return _ -> true
    | I.Seq _ -> true
    | I.Unary _ -> true
    | I.Var _ -> true
    | I.VarDecl _ -> true
    | I.While _ -> true
    | _ -> true
  in
  true


let gen_view_from_proc iprog iproc=
  (*
    - pred name
    - parameter list = method.para + option res + #e
    - parse body
  *)
  let pred_name = iproc.I.proc_name ^ "_v" in
  let r_args = match iproc.I.proc_return with
    | Void -> []
    | _ -> let r_arg =  "#res" in
      [r_arg]
  in
  let e_arg = "#e" in
  let pred_args = (List.map (fun para -> para.I.param_name) iproc.I.proc_args) @ r_args @ [e_arg] in
  true

let gen_view_from_prog iprog iproc=
  false

(* O: safe, 1: unsafe, 2: unknown, 3: not applicaple *)
let verify_as_sat iprog=
  2
