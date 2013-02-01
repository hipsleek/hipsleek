(* regex.ml - regular expression matching for OCaml *)

module R = Str

type r = R.regexp
type m = bool * string

let regex (x:string) : r = R.regexp x

let is_match (r:r) (x:string) : bool = R.string_match r x 0

let rmatch (r:r) (x:string): m = (is_match r x, x)

let success ((b,_):m) : bool = b

let group ((_,s):m) (i:int) : string = R.matched_group i s

let split (r:r) (x:string) : string list = R.split r x

(* [replace r x x0]: replace r by x in x0 *)
let replace (r:r) (x:string) (x0:string) : string = R.global_replace r x x0
