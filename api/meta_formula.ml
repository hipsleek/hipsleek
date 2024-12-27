open Hipsleek_common
open Common_util

(* type t = Sleekcommons.meta_formula *)
module Normal = struct
  type t = {heap_formula : Heap_formula.t; pure_formula: Pure_formula.t}
  let of_heap_and_pure heap_formula pure_formula = {heap_formula; pure_formula}
  let to_sleek_formula {heap_formula; pure_formula} =
    let open Iformula in
    Iformula.Base({
      formula_base_heap = Heap_formula.to_sleek_formula heap_formula;
      formula_base_pure = Pure_formula.to_sleek_formula pure_formula;
      formula_base_vperm = IvpermUtils.empty_vperm_sets;
      formula_base_flow = "__norm";
      formula_base_and = [];
      formula_base_pos = no_pos})

  let of_sleek_formula = function
    | Iformula.Base({ formula_base_heap; formula_base_pure; _ }) ->
        of_heap_and_pure (Heap_formula.of_sleek_formula formula_base_heap) (Pure_formula.of_sleek_formula formula_base_pure)
    | _ -> failwith "Unsupported SLEEK Iformula" (* TODO more descriptive error *)

  let to_string formula = Sleekcommons.string_of_meta_formula (Sleekcommons.MetaForm (to_sleek_formula formula))

end

module Structured = struct
  type t = {heap_formula : Heap_formula.t; pure_formula: Pure_formula.t}

  let of_heap_and_pure heap_formula pure_formula = {heap_formula; pure_formula}

  let to_sleek_formula {heap_formula; pure_formula} =
    let base_formula = Normal.to_sleek_formula (Normal.of_heap_and_pure heap_formula pure_formula) in
    Iformula.EBase {Iformula.formula_struc_explicit_inst = [];
      Iformula.formula_struc_implicit_inst = [];
      Iformula.formula_struc_exists = [];
      Iformula.formula_struc_base = base_formula;
      Iformula.formula_struc_is_requires = false; (* Not sure what this is *)
      Iformula.formula_struc_continuation = None;
      Iformula.formula_struc_pos = no_pos}

  let of_sleek_formula = function
    | Iformula.EBase({formula_struc_base = Iformula.Base({formula_base_heap; formula_base_pure; _}); _})
    -> {heap_formula = Heap_formula.of_sleek_formula formula_base_heap;
        pure_formula = Pure_formula.of_sleek_formula formula_base_pure}
    | _ -> failwith "Unsupported SLEEK Iformula"

  let to_string formula = Sleekcommons.string_of_meta_formula (Sleekcommons.MetaEForm (to_sleek_formula formula))
end
