type t =
  | Anonymous of string
  | Normal of string
  | Primed of string

let make s = Normal s
let anon () = Anonymous (Hipsleek_common.Globals.fresh_trailer ())
let primed s = Primed s

let is_primed = function
  | Primed _ -> true
  | _ -> false

let is_anon = function
  | Anonymous  _ -> true
  | _ -> false

let to_sleek_name = function
  | Anonymous s -> s
  | Normal s -> s
  | Primed s -> s

let to_string = function
  | Anonymous s -> Printf.sprintf "[anon var %s]" s
  | Normal s -> s
  | Primed s -> s ^ "'"

let to_sleek_ident = function
  | Anonymous s | Normal s -> (s, Hipsleek_common.VarGen.Unprimed)
  | Primed s -> (s, Hipsleek_common.VarGen.Primed)

let of_sleek_ident (name, primed) =
  match primed with
  | Hipsleek_common.VarGen.Primed -> Primed name
  | Hipsleek_common.VarGen.Unprimed -> Normal name
