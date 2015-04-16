#include "xdebug.cppo"
open VarGen
(*
  XML front-end.

  Translate XML data to internal AST.
*)

open Globals
open Sleekcommons

module I = Iast
module IF = Iformula
module IP = Ipure

let to_data xml : I.data_decl =
  let dname = ref "" in
  (*let fld_list = ref [] in*)
  (*let f cld = 
	match Xml.tag cld with
	  | "cname" -> dname := (Xml.pcdata cld) (* (List.hd (Xml.children cld))) *)
	  | "" -> Error.report_error {Error.error_loc = no_pos; Error.error_text = "malfunction, pattern mismatch in to_data"}
  in*)
	{ I.data_name = !dname;
        I.data_pos = no_pos;
	  I.data_fields = [];
	  I.data_parent_name = "";
	  I.data_invs = [];
      I.data_is_template = false;
	  I.data_methods = [] }
  

let parse (input : string) : command =
  let xml = Xml.parse_string input in
	match Xml.tag xml with
	  | "class" -> 
		  let data_decl = to_data xml in
			DataDef data_decl
	  | _ -> failwith ("Not supported tag: " ^ Xml.tag xml)
