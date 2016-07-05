#include "xdebug.cppo"
open VarGen
(*
   Created 24 - 08 - 2006
   Sanity Checks
*)

open Globals
module I = Iast

(* receives a class and checks if there are no field names duplications within that class *)
let no_field_duplication_within_class (c : I.data_decl) : bool = 
  let flag = ref true in 
    begin
      List.iter
	(fun t1 -> let f1 = I.get_field_name t1 in (* An Hoa [22/08/2011] : modify to use function instead of hard code field name extraction *)
	  (List.iter
	     (fun t2 ->	let f2 = I.get_field_name t2 in (* An Hoa [22/08/2011] : modify to use function instead of hard code field name extraction *)
	       if (!flag = true) && (t1 != t2) && (f1 = f2) then
		 begin
		   print_string ("Field " ^ f1 ^ " from class " ^ c.I.data_name ^ " is duplicated \n");
		   flag := false;
		 end  		 
	     ) c.I.data_fields
	  )
	) c.I.data_fields;
      !flag;
    end


(* receives a class and checks if there are no method names duplications within that class *)
let no_method_duplication_within_class (c : I.data_decl) : bool = 
  let flag = ref true in 
    begin
      List.iter
	(fun t1 ->
	  (List.iter
	     (fun t2 ->
	       if (!flag = true) && (t1 != t2) && t1.I.proc_name = t2.I.proc_name then
		 begin
		   print_string ("Method " ^ t1.I.proc_name ^ " from class " ^ c.I.data_name ^ " is duplicated \n");
		   flag := false;
		 end  		 
	     ) c.I.data_methods
	  )
	) c.I.data_methods;
      !flag;
    end


(* receives two classes, c1 and c2, and returns true if c1 inherits c2, and false otherwise *)
let rec inherits (prog : I.prog_decl) (c1 : I.data_decl) (c2 : I.data_decl) : bool = match c1.I.data_parent_name with
  | "Object" -> false
  | _ -> 
      try 
      let parent = List.find (fun t -> t.I.data_name = c1.I.data_parent_name) prog.I.prog_data_decls in
        if parent.I.data_name = c2.I.data_name then true
        else inherits prog parent c2	  
      with
      | Not_found -> false

(* receives two classes and returns true if the classes are related - there is a inheritance relationship between them -, and false otherwise *)
let classes_related (prog : I.prog_decl) (c1 : I.data_decl) (c2 : I.data_decl) : bool = 
  (inherits prog c1 c2)|| (inherits prog c2 c1) 

(* receives two types and verifies if they are identic *)
let rec match_type (t1 : typ) (t2 : typ) : bool = 
  match t1 with
    | Named (i1) -> 
        begin 
	        match t2 with
	          | Named (i2) -> (i1 = i2)
	          | _ -> false
        end	      	
    | Array (t3, o3) -> 
        begin 
	        match t2 with
	          | Array (t4, o4) -> (o3 = o4) && (match_type t3 t4)
	          | _ -> false
        end 
    | _ -> match_type t1 t2

(* receives two procedures and checks if they have matching signatures *)
let match_signature (p1 : I.proc_decl) (p2 : I.proc_decl) = 
  if (p1.I.proc_name = p2.I.proc_name) then    (* I check types only if names are equal *)
    begin
      if (List.length p1.I.proc_args != List.length p2.I.proc_args) || not (match_type p1.I.proc_return p2.I.proc_return) then        false
      else    
	let matching_args = 
	  List.length 
	    (List.map2 
	       (fun t1 -> fun t2 -> 
		 ((match_type t1.I.param_type t2.I.param_type) && t1.I.param_mod = t2.I.param_mod)) p1.I.proc_args p2.I.proc_args) 
	  = List.length p1.I.proc_args in
	matching_args 
    end
  else true

(* checks if there is any overridding conflict between methods - a method is overridden with a different signature *)
let overridding_correct (prog : I.prog_decl) : bool = 
  let flag = ref true in
  begin
    List.iter
      (fun t1 -> (* t1 is a class *)
	(List.iter
	  (fun t2 -> (* t2 is a method *)
	    (List.iter
	      (fun t3 -> (* t3 is a class *)
		(List.iter
		   (fun t4 -> (* t4 is a method *)
		     if !flag && (inherits prog t1 t3) && (not (match_signature t2 t4)) then 
		       begin
			 print_string ("Method " ^ t2.I.proc_name ^ " from class " ^ t3.I.data_name ^ " is overriden with a different signature in class " ^ t1.I.data_name ^ "\n");
			 flag := false;
		       end  
		     (*else print_string ("Overridding test for  method " ^ t2.I.proc_name ^ "... overridding correct\n")  *)              
		   )
		) t3.I.data_methods
	      ) 
	    ) prog.I.prog_data_decls
	  ) t1.I.data_methods 
	) 
      ) (List.rev prog.I.prog_data_decls);
    !flag;  
    end

(* checks if there is any field hiding within the class hierarchy *)
let no_field_hiding (prog : I.prog_decl) : bool = 
  let flag = ref true in
  begin
    List.iter
      (fun t1 -> (* t1 is a class *)
	(List.iter (* An Hoa [22/08/2011] : Add let f2 and let f4 instead of hard code *)
	  (fun t2 -> let f2 = I.get_field_name t2 in (* t2 is a field *)
	    (List.iter
	      (fun t3 -> (* t3 is a class *)
		(List.iter
		   (fun t4 -> let f4 = I.get_field_name t4 in (* t4 is a field *)
		     if !flag && t1 != t3 && (inherits prog t1 t3) && (f2 = f4) then 
		       begin
			 print_string ("Field " ^ f2 ^ " from class " ^ t3.I.data_name ^ " is hidden by a declaration in class " ^ t1.I.data_name ^ "\n");
			 flag := false;
		       end  
                  )
		) t3.I.data_fields
	      ) 
	    ) prog.I.prog_data_decls
	  ) t1.I.data_fields 
	) 
      ) (List.rev prog.I.prog_data_decls);
    !flag;  
    end


(* receives a prog and checks if there is any field duplication within any class *)
let no_field_duplication (prog : I.prog_decl) : bool = 
  List.for_all no_field_duplication_within_class prog.I.prog_data_decls

(* receives a prog and checks if there is any method duplication within any class *)
let no_method_duplication (prog : I.prog_decl) : bool = 
  List.for_all no_method_duplication_within_class prog.I.prog_data_decls

(* some test printing *)
let rec print_class_procs (procs : I.proc_decl list) = match procs with
| [] -> "\n"
| p :: rest -> "Proc " ^ p.I.proc_name ^ "\n" ^ print_class_procs rest


let rec print_procs (data : I.data_decl list) = match data with
| [] -> "\n"
| d :: rest -> print_class_procs d.I.data_methods ^ print_procs rest  

   




