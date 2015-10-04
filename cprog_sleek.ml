#include "xdebug.cppo"
(** pretty printing for formula and cast *)

open Format
open Globals
open VarGen
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Lexing
open Cast
open Cformula
open Mcpure_D
open Gen.Basic
(* open Label_only *)
open Printf

module LO = Label_only.LOne
module LO2 = Label_only.Lab2_List
module P = Cpure
module MP = Mcpure
module CVP = CvpermUtils

let cprog = ref { 
    Cast.prog_data_decls = [];
    Cast.prog_view_decls = [];
    Cast.prog_logical_vars = [];
    Cast.prog_rel_decls = (let s = new Gen.stack_pr "prog_rel_decls(CAST)" Cprinter.string_of_rel_decl (=) in s);
    Cast.prog_templ_decls = [];
    Cast.prog_ui_decls = [];
    Cast.prog_ut_decls = [];
    Cast.prog_hp_decls = [];
    Cast.prog_view_equiv = [];
    Cast.prog_axiom_decls = []; 
    (* [4/10/2011] An Hoa *)
    (*Cast.old_proc_decls = [];*)
    Cast.new_proc_decls = Hashtbl.create 1; (* no need for proc *)
    (*Cast.prog_left_coercions = [];
      Cast.prog_right_coercions = [];*)
    Cast. prog_barrier_decls = []} ;;

let get_sorted_view_decls () =
  let vdefs = Cast.sort_view_list !cprog.Cast.prog_view_decls in
  !cprog.Cast.prog_view_decls <- vdefs;
  vdefs

let update_view_decl_cprog vdef = 
  Cast.update_view_decl !cprog vdef


let update_view_decl_iprog vdef = 
  try
    let iprog = Iast.get_iprog () in
    Iast.update_view_decl iprog vdef
  with _ -> failwith (x_loc^" iprog not found")
