#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module SProt  = Session.IProtocol
module SBProt = Session.IProtocol_base
module SIOrd = Session.IOrders
module OS = Order_summary
module SProj = Session.IProjection
module SBProj = Session.IProjection_base
module STProj = Session.ITPProjection
module SBTProj = Session.ITPProjection_base

type role = SIOrd.role
type chan = SIOrd.chan


module Projection_map = 
struct
  type t = SProj.session 
  type base = SProj.t

  let bot () = failwith x_tbi
  let is_bot x = failwith x_tbi
  let eq e1 e2 = failwith x_tbi
  let string_of f = SProj.string_of_session f
  let mk_base (base: base) : t = failwith x_tbi
  let mk_or   (or1:t) (or2:t) : t = failwith x_tbi 
  let mk_star (star1:t) (star2:t) : t = failwith x_tbi 
  let merge_seq (f1:t) (f2:t) : t = failwith x_tbi
  let merge_sor (f1:t) (f2:t) : t = failwith x_tbi
  let merge_star (f1:t) (f2:t) : t = failwith x_tbi
  let mkSingleton (e:base) : t = failwith x_tbi
  let add_elem (old_e:t) (new_e:t) :t  = failwith x_tbi

end;;

module TProjection_map =
struct
  type t = STProj.session
  type base = STProj.t

  let bot () = failwith x_tbi
  let is_bot x = failwith x_tbi
  let eq e1 e2 = failwith x_tbi
  let string_of f = STProj.string_of_session f
  let mk_base (base: base) : t = failwith x_tbi
  let mk_or   (or1:t) (or2:t) : t = failwith x_tbi 
  let mk_star (star1:t) (star2:t) : t = failwith x_tbi 
  let merge_seq (f1:t) (f2:t) : t = failwith x_tbi
  let merge_sor (f1:t) (f2:t) : t = failwith x_tbi
  let merge_star (f1:t) (f2:t) : t = failwith x_tbi
  let mkSingleton (e:base) : t = failwith x_tbi
  let add_elem (old_e:t) (new_e:t) :t  = failwith x_tbi
end;;

module PrjMap = OS.SMap(OS.IRole)(Projection_map)
module TPrjMap = OS.SMap(OS.IChan)(TProjection_map)

let mk_projection_per_party prot (* role *) =
  let deconstruct_prot prot = match prot with
    | SProt.SBase sb -> 
        begin
          match sb with
          | SProt.Base base ->
            let msg_var = SBProt.get_message_var base in
            let msg = SBProt.get_message base in
            let chan = SBProt.get_chan base in

            let () = print_endline ("elena msg_var: " ^ (SBProt.print_var msg_var)) in
            let () = print_endline ("elena msg: " ^ (!Session.IForm.print msg)) in
            let c = match chan with
            | Some ch -> SBProt.string_of_chan ch
            | None -> "" in
            let () = print_endline ("elena msg_chan: " ^ c) in
            let () = print_endline ("elena Base: " ^ (SProt.string_of_session_base sb)) in
            None
          | SProt.Predicate sp ->
            let () = print_endline ("elena Predicate: " ^ (SProt.string_of_session_base sb)) in
            None
          | _ -> None
      end
    | _ -> None
  in
  let fnc = (deconstruct_prot, (nonef, nonef)) in
  let res = SProt.trans_session_formula fnc prot in
  res

  
