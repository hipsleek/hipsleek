open Hipsleek_common
open Common_util

type t = Sleekcommons.meta_formula

let ante heap_f pure_f  =
  let formula_base = {
    Iformula.formula_base_heap = Heap_formula.to_sleek_formula heap_f;
    Iformula.formula_base_pure = Pure_formula.to_sleek_formula pure_f;
    Iformula.formula_base_vperm = IvpermUtils.empty_vperm_sets;
    Iformula.formula_base_flow = "__norm";
    Iformula.formula_base_and = [];
    Iformula.formula_base_pos = no_pos
  } in
  Sleekcommons.MetaForm(Iformula.Base(formula_base))

let conseq heap_f pure_f =
  let formula_base = {
    Iformula.formula_base_heap = Heap_formula.to_sleek_formula heap_f;
    Iformula.formula_base_pure = Pure_formula.to_sleek_formula pure_f;
    Iformula.formula_base_vperm = IvpermUtils.empty_vperm_sets;
    Iformula.formula_base_flow = "__norm";
    Iformula.formula_base_and = [];
    Iformula.formula_base_pos = no_pos
  } in
  let struc_base_formula = {
    Iformula.formula_struc_explicit_inst = [];
    Iformula.formula_struc_implicit_inst = [];
    Iformula.formula_struc_exists = [];
    Iformula.formula_struc_base = Base(formula_base);
    Iformula.formula_struc_is_requires = false; (* Not sure what this is *)
    Iformula.formula_struc_continuation = None;
    Iformula.formula_struc_pos = no_pos
  } in
  Sleekcommons.MetaEForm(Iformula.EBase(struc_base_formula))

let ante_printer xs =
  let rec ante_printer_aux i xs =
    match xs with
    | [] -> ""
    | x::xs' -> "Ante 1 : " ^ (Sleekcommons.string_of_meta_formula x) ^ "\n" ^
                (ante_printer_aux (i+1) xs')
  in
  ante_printer_aux 1 [xs]

let conseq_printer x =
  "Conseq : " ^ (Sleekcommons.string_of_meta_formula x)

let of_sleek_formula f = f
let to_sleek_formula f = f
