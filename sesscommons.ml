#include "xdebug.cppo"
open VarGen
open Globals

let event_rel_id: string option ref = ref None
let hb_rel_id: string option ref = ref None
let hbp_rel_id: string option ref = ref None
let cb_rel_id: string option ref = ref None
let sevent_rel_id: string option ref = ref None
let shb_rel_id: string option ref = ref None
let shbp_rel_id: string option ref = ref None
let scb_rel_id: string option ref = ref None

(* ======= base formula for session type ====== *)
(* ============================================ *)
module type Message_type = sig
  type formula
  type pure_formula
  type h_formula
  type h_formula_heap
  type ho_param_formula
  type struc_formula
  (* type node *)
  type param
  type var
  type flow
  type arg = var (* node *) * ident * (ho_param_formula list) *
             (param list) * VarGen.loc

  val is_emp : formula -> bool
  val print  : (formula -> string) ref
  val print_struc_formula  : (struc_formula -> string) ref
  val print_h_formula  : (h_formula -> string) ref
  val print_ho_param_formula  : (ho_param_formula -> string) ref
  val print_var  : (var -> string)
  val print_param: (param -> string) ref
  val print_pure_formula: (pure_formula -> string) ref
      
  val mk_node: arg -> session_kind -> node_kind -> h_formula
  val mk_formula_heap_only: ?flow:flow -> h_formula -> VarGen.loc -> formula
  val mk_rflow_formula: ?sess_kind:(session_kind option) -> ?kind:ho_flow_kind -> formula -> ho_param_formula
  val mk_rflow_formula_from_heap:  h_formula -> ?sess_kind:(session_kind option) -> ?kind:ho_flow_kind -> VarGen.loc -> ho_param_formula
  val mk_formula: pure_formula -> arg -> session_kind -> node_kind -> formula
  val mk_formula_of_pure_1: pure_formula -> VarGen.loc -> formula
  val mk_struc_formula: formula -> VarGen.loc -> struc_formula
  val mk_star: h_formula -> h_formula -> VarGen.loc -> h_formula
  val mk_star_formula: formula -> formula -> VarGen.loc -> formula
  val mk_exists: (ident * primed) list -> h_formula -> VarGen.loc -> formula
  val mk_or: formula -> formula -> VarGen.loc -> formula
  val mk_empty: unit -> h_formula
  val mk_true: unit -> pure_formula
  val mk_hvar: ident -> var list -> h_formula
  val mk_seq_wrapper: ?sess_kind:session_kind option -> h_formula -> VarGen.loc -> session_kind -> h_formula
  val mk_exp_rel: ident -> (var * VarGen.loc) list -> VarGen.loc -> pure_formula 

  val choose_ptr: ?ptr:string -> unit -> var (* node *)
  val id_to_param:  ident ->  VarGen.loc -> param
  val const_to_param:  int ->  VarGen.loc -> param
  val fconst_to_param:  float ->  VarGen.loc -> param
  val var_to_param: var ->  VarGen.loc -> param
  val param_to_var: param -> var

  val add_pure_to_formula: pure_formula -> formula -> formula
  val transform_h_formula: (h_formula -> h_formula option)-> h_formula -> h_formula
  val transform_formula: (h_formula -> h_formula option)-> formula -> formula
  val transform_struc_formula:  (h_formula -> h_formula option)-> struc_formula -> struc_formula
  val transform_struc_formula_formula:  (formula -> formula option)-> struc_formula -> struc_formula
  val map_one_rflow_formula: (formula -> formula) -> ho_param_formula -> ho_param_formula
  val map_rflow_formula_list: (formula -> formula) -> ho_param_formula list -> ho_param_formula list
  val map_rflow_formula_list_res_h: (formula -> formula) -> h_formula_heap -> h_formula
  val update_temp_heap_name: view_session_info -> h_formula -> h_formula option
  val set_heap_node_var: var -> h_formula_heap -> h_formula
  val set_anns: h_formula -> sess_ann -> h_formula
  val subst_param:   (var * var) list -> param -> param
  val subst_var:     (var * var) list -> var -> var
  val subst_formula: (var * var) list -> formula -> formula
  val fresh_var: var -> var
  val eq_var: var -> var -> bool
  val mk_var: ident -> var
  val append_tail: h_formula -> h_formula -> h_formula
  val join_conjunctions: pure_formula list -> pure_formula

  val is_base_formula: formula -> bool
  val is_exists_formula: formula -> bool
  val get_h_formula: formula -> h_formula
  val get_pure_formula: formula -> pure_formula
  val get_h_formula_safe: formula -> h_formula
  val get_h_formula_from_ho_param_formula: ho_param_formula -> h_formula
  val get_formula_from_ho_param_formula: ho_param_formula -> formula
  val get_ho_param: h_formula_heap -> ho_param_formula list
  val get_node: h_formula -> arg
  val get_or_formulae: formula -> formula list
  val get_star_formulae: h_formula -> h_formula list
  val get_star_pos: h_formula -> VarGen.loc
  val get_param_id: param -> ident
  val get_node_id: var(* node *) -> ident
  val get_formula_from_struc_formula: struc_formula -> formula
  val get_hvar: h_formula -> ident * var list
  val get_session_info: h_formula -> view_session_info option
  val get_view_session_info:  h_formula_heap -> view_session_info option
  val get_node_kind: h_formula -> node_kind
  val get_session_kind: h_formula -> session_kind option
  val get_heap_node: h_formula -> h_formula option
  val get_node_only: h_formula -> h_formula_heap
  val get_node_opt:  h_formula -> h_formula_heap option
  val get_heap_node_var: h_formula_heap -> var
  val get_anns: h_formula -> sess_ann option
  val get_exists_vars: formula -> (ident * primed) list
  val get_formula_pos: formula -> VarGen.loc
      
  val get_h_formula_safe: formula -> h_formula option
  val get_h_formula_from_struc_formula_safe: struc_formula -> h_formula option

end;;

(* ------------------------------ *)
(* --- boundary base elements --- *)
module type ELEMENT_TYPE =
sig
  type t
  val string_of : t -> string
  val eq        : t -> t -> bool
  val add_elem  : t ->t -> t
end;;

(* ------------------------------ *)
(* ------ boundary elements ----- *)
module type BOUNDARY_ELEMENT_TYPE =
sig
  include ELEMENT_TYPE

  type base
  val bot       : unit -> t
  val is_bot    : t -> bool
  val mk_base    : base -> t
  val mk_or      : t -> t -> t
  val mk_star    : t -> t -> t
  val merge_seq  : t -> t -> t
  val merge_sor  : t -> t -> t
  val merge_star : t -> t -> t
end;;

(* ------------------------------------------------ *)
(* singnature of the keys for the backtier/frontier *)
module type KEY_EQ_TYPE =
sig
  type t
  val eq        : t -> t -> bool
  val string_of : t -> string   
end;;

(* ====== General SMap utilities ====== *)
(* ==================================== *)

module type GSMap_type =
sig

  type key
  type elem
  type emap
  type epart
  type elist
  type klist

  val eq: key -> key -> bool

  val string_of_elem : elem -> string
  val string_of_key  : key -> string
  val string_of:  emap -> string
    
  val mkEmpty : emap
  val is_empty :emap -> bool

  val mkSingleton : key -> elem -> emap
  val init : (key * elem) list -> emap
    
  val add : emap-> key -> elem -> emap
  val find: emap -> key -> elem
  val find_unsafe: emap -> key -> elem
  val get_keys : emap -> klist
  val get_data : emap -> elist

  val update_elem    : emap -> key -> elem -> emap
  val add_elem_dupl  : emap -> key -> elem -> emap
  val add_elem       : emap -> key -> elem -> emap

end;;

module GSMap
    (Key  : KEY_EQ_TYPE)
    (Elem : ELEMENT_TYPE) =
struct
  type key  = Key.t
  type elem = Elem.t
  type emap = (key * elem) list
  type epart = (elem list) list
  type elist = (elem list)
  type klist = (key list) 

  let eq = Key.eq 
  let string_of_elem = Elem.string_of
  let string_of_key  = Key.string_of 

  let string_of (e: emap) : string =    
    "["^ (pr_lst "," (pr_pair string_of_key string_of_elem) e) ^"]"
    
  let mkEmpty () : emap = []
  let is_empty (m:emap) = match m with | [] -> true | _ -> false

  let mkSingleton (key:key) (elem:elem) : emap = [(key,elem)]
  let init lst : emap = lst

  let find_aux (s: emap) (k:key) (d:elem) : elem =
    try
      snd(List.find (fun (k0,_) -> eq k0 k) s)
    with
      _ -> d

  let find (s : emap) (k: key) : elem  = snd(List.find (fun (k0,_) -> eq k0 k) s)

  let remove_duplicate_keys (keys:klist) : klist =
    let keys = List.fold_left (fun acc key ->
        if List.exists (eq key) acc then acc
        else (key::acc)) [] keys in
    keys

  (* each key is returned only once *)
  let get_keys (s : emap) : klist =
    let all_keys = List.map fst s in
    remove_duplicate_keys all_keys

  let get_data (emap:emap) : elist = List.map snd emap
  
  (* each key is returned only once *)
  let union_keys (e1:klist) (e2:klist) : klist =
    remove_duplicate_keys (e1@e2)

  let update_elem (e1:emap) (k:key) (el:elem) : emap =
    List.map (fun (k0,e0) -> if Key.eq k0 k then (k0, Elem.add_elem e0 el) else (k0,e0)) e1

  (* allow key duplicates *)
  let add_elem_dupl (e1:emap) (k:key) (el:elem) : emap =
    (k,el)::e1
    
  (* if key exists in emap, then replace its corresponding element *)
  let add_elem (e1:emap) (k:key) (el:elem) : emap =
    try 
      let _ = find e1 k in (* only checks if the key exists in map *)
      update_elem e1 k el
    with Not_found -> add_elem_dupl e1 k el

  let map_data_ext (fnc: elem->'a) (map: emap) : (key * 'a) list  = List.map (fun (k,elem) -> (k, fnc elem)) map
end;;

(* ====== SMap utilities ====== *)
(* ============================ *)
module type SMap_type =
sig
  include GSMap_type

  val union      : emap -> emap -> emap
  val merge_seq  : emap -> emap -> emap
  val merge_sor  : emap -> emap -> emap
  val merge_star : emap -> emap -> emap 
  val map_data   : (elem -> elem) -> emap -> emap

end;;

module SMap
    (Key  : KEY_EQ_TYPE)
    (Elem : BOUNDARY_ELEMENT_TYPE) =
struct
  include GSMap(Key)(Elem)

  (* this merge allows duplicates *)
  let union_dupl (e1:emap) (e2:emap) : emap =
    e1 @ e2

  (* TODO Andreea : debug below add/update_elem?*)
  (* this merge assumes e1 and e2 have no key duplicates *)
  let union (e1:emap) (e2:emap) : emap =
    List.fold_left (fun acc (key,elem) -> add_elem acc key elem) e1 e2

  let union (e1:emap) (e2:emap) : emap =
    let pr = string_of in
    Debug.no_2 "union" pr pr pr union e1 e2 
      
  (* this merge assumes e1 and e2 have no key duplicates *)
  let flatten (e0:emap list) : emap =    
    List.fold_left (fun acc e1 -> union acc e1) (mkEmpty ()) e0

  let flatten (e0:emap list) : emap =
    let pr = string_of in
    Debug.no_1 "flatten" (pr_list pr) pr flatten e0
  
  type op = SEQ | SOR | STAR

  (* generic merge emap function *)
  let merge_op op (e1:emap) (e2:emap) : emap =
    let merge_elem op =
      match op with
      | SEQ  -> Elem.merge_seq
      | SOR  -> Elem.merge_sor
      | STAR -> Elem.merge_star in
    List.fold_left (fun map (key,elem) ->
        let elem1 = find map key in (* \bot or some element *)
        let elem1 = (merge_elem op) elem1 elem in
        add_elem map key elem1) e1 e2 
    
  let merge_seq  (e1:emap) (e2:emap) :emap = merge_op SEQ e1 e2 
  let merge_sor  (e1:emap) (e2:emap) :emap = merge_op SOR e1 e2
  let merge_star (e1:emap) (e2:emap) :emap = merge_op STAR e1 e2

  let map_data (fnc: elem->elem) (map: emap) : emap = List.map (fun (k,elem) -> (k, fnc elem)) map
  
  (* find element with key k in s *)
  let find_safe (s : emap) (k: key) : elem  = find_aux s k (Elem.bot ())


end;;


