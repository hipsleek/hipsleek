open Globals

type z3m_val = 
  | Z3_Int of int
  | Z3_Frac of (float * float)

type z3m_res =
  | Z3m_Unsat
  | Z3m_Sat_or_Unk

let string_of_z3m_val = function
  | Z3_Int i -> string_of_int i
  | Z3_Frac (f1, f2) -> (string_of_float f1) ^ "/" ^ (string_of_float f2)

let string_of_z3m_res = function
  | Z3m_Unsat -> "Unsat"
  | Z3m_Sat_or_Unk -> "Sat or Unk"

let z3m_val_mult v1 v2 = 
  match v1, v2 with
  | Z3_Int i1, Z3_Int i2 -> Z3_Int (i1 * i2)
  | Z3_Int i1, Z3_Frac (n2, d2) -> Z3_Frac ((float_of_int i1) *. n2, d2)
  | Z3_Frac (n1, d1), Z3_Int i2 -> Z3_Frac (n1 *. (float_of_int i2), d1)
  | Z3_Frac (n1, d1), Z3_Frac (n2, d2) -> Z3_Frac (n1 *. n2, d1 *. d2)

let z3m_val_neg v = 
  match v with
  | Z3_Int i -> Z3_Int (-i)
  | Z3_Frac (n, d) -> Z3_Frac (-.n, d)

exception Invalid_Z3m_val 

let z3m_val_to_int (vl: z3m_val list): int list =
  let int_of_float (f: float) = 
    let i = truncate f in
    if (float_of_int i) = f then i
    else raise Invalid_Z3m_val 
  in
  let den_l = List.fold_left (fun a v -> match v with
    | Z3_Int _ -> a | Z3_Frac (_, d) -> a @ [int_of_float d]) [] vl in
  let den_lcm = lcm_l den_l in
  List.map (fun v -> match v with
    | Z3_Int i -> i * den_lcm
    | Z3_Frac (n, d) -> (int_of_float n) * den_lcm / (int_of_float d) 
  ) vl

let z3m_val_to_int (vl: z3m_val list): int list =
  let pr1 = pr_list string_of_z3m_val in
  let pr2 = pr_list string_of_int in
  Debug.no_1 "z3m_val_to_int" pr1 pr2 z3m_val_to_int vl

