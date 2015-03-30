#include "xdebug.cppo"
open VarGen
(*
  Created 19-Feb-2006

  Environment:
   - Symbol table handling stuff
   - Scoping
   - Alpha-renaming
   - Constant/Enum substitution
*)

open Globals

module H = Hashtbl
module I = Iast
module C = Cast

type sym_tab = (ident, ident_info) H.t

and ident_info =
  | VarInfo of var_info (* variable and parameter *)
  | ConstInfo of const_info (* constants of various types *)
  | EnumInfo of enum_info (* including numeric values, enum name 
							 (two enum values won't match if they 
							 have different enum name) *)

and var_info = { var_name : ident;
				 var_alpha : ident;
				 var_type : typ }

and const_info = { const_name : ident;
				   const_type : typ;
				   const_value : C.exp } (* this must be a constant value *)

and enum_info = { enum_name : ident; (* name of the enum constant *)
				  enum_type : typ; (* name of the enum type is used in EType *)
				  enum_value : int } (* enum_name's numeric value *)


(* maintain a list of scopes *)
let scopes : sym_tab list ref = ref []

(* push/pop scopes *)

let push_scope () = 
  let new_scope = H.create 19 in
	scopes := new_scope :: !scopes

let pop_scope () =
  if Gen.is_empty !scopes then
	failwith ("no more scope to pop")
	  (* note that this error shouldn't happen for a well-formed input,
		 so if it does happen, there must be something wrong with the analyzer *)
  else
	scopes := List.tl !scopes

let clear () = scopes := []

(*
(* clear names in current scope *) 
let clear_names (names : ident list) = 
*)

(* look up information associated with v, 
   raises Not_found if v is not present *)
let rec look_up (v : ident) : ident_info =
  let rec helper cur_scopes = 
	if Gen.is_empty cur_scopes then
	  raise Not_found
	else
	  let top_scope = List.hd cur_scopes in
		try
		  H.find top_scope v
		with
		  | Not_found -> helper (List.tl cur_scopes)
  in
	helper !scopes

and add (v : ident) (i : ident_info) =
  if Gen.is_empty !scopes then
	failwith ("no scope to add")
	  (* note that this error shouldn't happen for a well-formed input,
		 so if it does happen, there must be something wrong with the analyzer *)  else
	let top_scope = List.hd !scopes in
	  H.add top_scope v i

(* 
   returns the alpha name of variable v. An alpha name is formed
   by appending to v a string formed by a unique string and a number.

   How to generate alpha name to ensure that there's no name clash?
   Supposing that the unique string exists (by, for example, having
   the lexer reject such string in the program text)

   If v already appears in any of the outer scope, 
*)

and alpha_name (v : ident) : ident = 
  if name_clash v then
	failwith ("alpha_name: name clash happens")
  else
	try
	  let (todo_unk:ident_info) = look_up v in (* name shadowing *)
	  let fi = fresh_int () in
		v ^ "__fr_fr__" ^ (string_of_int fi)
	with
	  | Not_found -> v (* no name shadowing, no need to do alpha renaming *)

(* returns true if there is a name clash, i.e. v is
   already in the top scope *)
and name_clash (v : ident) : bool =
  if Gen.is_empty !scopes then
	false
  else
    let top_scope = List.hd !scopes in
    try
      let todo_unk = H.find top_scope v in
      true
    with
      | Not_found -> false

(*
  all visible names in the current scope
  - all (alpha-converted) names in the current scope
  - how about names in parent scopes???

  - a safe solution: all names in the environment are
    returned. due to alpha-conversion, no colisions
    will occur.
*)

and names_on_top () : I.typed_ident list = 
  if Gen.is_empty !scopes then
	[]
  else
	let top_infos = Gen.HashUti.list_of_hash_values (List.hd !scopes) in
	let top_names = List.map name_of_info top_infos in
	  top_names

and visible_names () : I.typed_ident list = 
  let all_infos = List.concat (List.map Gen.HashUti.list_of_hash_values !scopes) in
  let all_names = List.map name_of_info all_infos in
	all_names

and name_of_info (i : ident_info) : I.typed_ident = match i with
  | VarInfo vi -> (vi.var_type, vi.var_alpha) (*JUSTFIX: just changed from var_name to var_alpha *)
  | ConstInfo ci -> (ci.const_type, ci.const_name)
  | EnumInfo ei -> (ei.enum_type, ei.enum_name)

and replace_type_info (i : ident_info) (t : typ) = match i with
  | VarInfo vi -> VarInfo {vi with var_type = t}
  | ConstInfo ci -> ConstInfo {ci with const_type = t}
  | EnumInfo ei -> EnumInfo {ei with enum_type = t}

(*
and remove (v : ident) = 
  let rec helper scopes = match scopes with
	| top :: rest -> begin
		try 
		  let vinfo = H.find top v in
			H.remove top v;
			vinfo
		with
		  | Not_found -> helper rest
	  end
	| [] -> ()
  in
	helper !scopes
*)

and replace_type (v : ident) (t : typ) =
  let rec helper scopes = match scopes with
	| top :: rest -> begin
		try 
		  let vinfo = H.find top v in
		  let new_info = replace_type_info vinfo t in
			H.replace top v new_info
		with
		  | Not_found -> helper rest
	  end
	| [] -> ()
  in
	helper !scopes
