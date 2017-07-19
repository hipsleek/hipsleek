#include "xdebug.cppo"
open VarGen

open Globals
open Gen.Basic
open Printf
open Gen.BList

module S = Session
module SC = Sesscommons

module Orders_relation_key (Form: SC.Message_type) =
struct
  type t = Form.var

  let eq e1 e2 = Form.eq_var e1 e2 
  let string_of f = Form.print_var f
end;;

module Orders_relation_elem (Form: SC.Message_type) =
struct 
  type t = Form.var * Form.var

  let eq (e11, e12) (e21, e22) = (Form.eq_var e11 e21) && (Form.eq_var e21 e22)
  let string_of (e1, e2) = pr_pair Form.print_var Form.print_var (e1,e2)
  let add_elem (old_e:t) (new_e:t) : t  = new_e
end;;

(* orders relations cformula map *)
module ORCMap = SC.GSMap(Orders_relation_key(S.CForm))(Orders_relation_elem(S.CForm))


