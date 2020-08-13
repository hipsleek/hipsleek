#include "xdebug.cppo"
open VarGen
open Globals
open Gen

type z3m_val = 
  | Int of int
  | Frac of (float * float)

let string_of_z3m_val = function
  | Int i -> string_of_int i
  | Frac (f1, f2) -> (string_of_float f1) ^ "/" ^ (string_of_float f2)

type z3m_res =
  | Unsat of ident list
  | Sat_or_Unk of (string * z3m_val) list 

let string_of_z3m_res = function
  | Unsat unsat_core -> "Unsat" ^ (pr_list idf unsat_core)
  | Sat_or_Unk m -> "Sat or Unk: " ^
                    (pr_list (pr_pair (fun s -> s) string_of_z3m_val) m)

let z3m_val_mult v1 v2 = 
  match v1, v2 with
  | Int i1, Int i2 -> Int (i1 * i2)
  | Int i1, Frac (n2, d2) -> Frac ((float_of_int i1) *. n2, d2)
  | Frac (n1, d1), Int i2 -> Frac (n1 *. (float_of_int i2), d1)
  | Frac (n1, d1), Frac (n2, d2) -> Frac (n1 *. n2, d1 *. d2)

let z3m_val_neg v = 
  match v with
  | Int i -> Int (-i)
  | Frac (n, d) -> Frac (-.n, d)

exception Invalid_Z3m_val 

let z3m_val_to_int (vl: z3m_val list): int list =
  let int_of_float (f: float) = 
    let i = truncate f in
    if (float_of_int i) = f then i
    else raise Invalid_Z3m_val 
  in
  let den_l = List.fold_left (fun a v -> match v with
      | Int _ -> a | Frac (_, d) -> a @ [int_of_float d]) [] vl in
  let den_lcm = lcm_l den_l in
  List.map (fun v -> match v with
      | Int i -> i * den_lcm
      | Frac (n, d) -> (int_of_float n) * den_lcm / (int_of_float d) 
    ) vl

let z3m_val_to_int (vl: z3m_val list): int list =
  let pr1 = pr_list string_of_z3m_val in
  let pr2 = pr_list string_of_int in
  Debug.no_1 "z3m_val_to_int" pr1 pr2 z3m_val_to_int vl

