(* std - standard functions *)

let identity (x:'a) : 'a = x
let compose (f:'b -> 'c) (g:'a -> 'b) (x:'a) = f (g x)
let sequence (f:'a -> 'b) (g:'b -> 'c) (x:'a) = g (f x)

let flip (f:'a -> bool) (x:'a) : bool = not (f x)
let neg (f:'a -> int) (x:'a) : int = (-1) * (f x)
let neg2 (f:'a -> 'b -> int) (x:'a) (y:'b) : int = (-1) * (f x y)
let rcompare (x:'a) (y:'b) : int = (-1) * (compare x y)

let lift (f:'b) (_:'a) = f

let fprint : out_channel -> string -> unit = output_string


let kprintf f fmt = Printf.ksprintf f fmt (* F# bug: omission *)
let fail format = kprintf failwith format
let showf format = Printf.sprintf format
let printf format = Printf.printf format
let fprintf f format = Printf.fprintf f format

let int_fcode (f:out_channel) : int -> unit = fprintf f "%d"

let even (x:int) : bool = (x mod 2 = 0)
let odd (x:int) : bool = (x mod 2 = 1)
let cram (x:int) (a:int) (b:int) : int = max a (min x b)
let get1 ((x,_,_):'a * 'b * 'c) : 'a = x
let get2 ((_,y,_):'a * 'b * 'c) : 'b = y
let get3 ((_,_,z):'a * 'b * 'c) : 'c = z
let map2 (f:'a -> 'b) ((x1,x2):'a * 'a) : 'b * 'b = (f x1, f x2)

let is_none : 'a option -> bool = function
  | None -> true
  | Some _ -> false

let is_some : 'a option -> bool = function
  | None -> false
  | Some _ -> true

let opt_get : 'a option -> 'a = function
  | None -> raise Not_found
  | Some x -> x

let opt_map (f:'a -> 'b) : 'a option -> 'b option = function
  | None -> None
  | Some x -> Some (f x)

let opt_some (f:'a -> bool) : 'a option -> bool = function
  | None -> false
  | Some x -> f x

let opt_iter (f:'a -> unit) : 'a option -> unit = function
  | None -> ()
  | Some x -> f x

let opt_list : 'a list option -> 'a list = function
  | None -> []
  | Some s -> s

let opt_map_list (f:'a -> 'b list) (s:'a option) = opt_list (opt_map f s)

let rec repeat (f:'a -> 'a) (n:int) (x:'a) : 'a =
  if n<=0 then x else repeat f (n-1) (f x)

let opt_show (f:'a -> string) : 'a option -> string = function
  | None -> ""
  | Some x -> f x

let opt_sexp (f:'a -> string) : 'a option -> string = function
  | None -> "None"
  | Some x -> "(Some " ^ f x ^ ")"

let char_show (c:char) : string = String.make 1 c
let bool_show = string_of_bool
let bool_bin (x:bool) : string = if x then "1" else "0"
let int_show = string_of_int
let int32_show = Int32.to_string
let int64_show = Int64.to_string
let float_show = string_of_float
let if_show s x = if x then s else ""
let bool_src s x = if x then s else ""
let int32_of = Int32.of_int
let int32_to = Int32.to_int
let int64_of = Int64.of_int
let int64_to = Int64.to_int

let int_char_show (x:int) : string =
  if (Char.code 'A' <= x && x <= Char.code 'Z')
  || (Char.code 'a' <= x && x <= Char.code 'z')
  then char_show (Char.chr x) else int_show x

let show (x:'a) : string = Compat.show x

let show2 ((x,y):'a * 'b) : string = 
  "(" ^ show x ^ ", " ^ show y ^ ")"

let show2_by (f1:'a1 -> string) (f2:'a2 -> string) 
  ((a1,a2):'a1 * 'a2) : string = "(" ^ f1 a1 ^ ", " ^ f2 a2 ^ ")"

let code2 : ('a -> string) -> ('b -> string) 
  -> 'a * 'b -> string = show2_by

let show3 ((x,y,z):'a * 'b * 'c) : string = 
  "(" ^ show x ^ ", " ^ show y ^ "," ^ show z ^ ")"


let str_print : string -> unit = print_string
let str_printx (a:string) : unit = print_endline a
let print (x:string) : unit = print_string x
let printl (x:string) : unit = print_endline x
let printlf format = kprintf printl format
let printx (a:'a) : unit = str_printx (show a)
let flush () : unit = Pervasives.flush stdout
let int_print (x:int) : unit = print (int_show x)
let bool_print (x:bool) : unit = print (bool_show x)

let unless (a:'a option) (f:unit -> 'b) : 'a =
  match a with Some x -> x | None -> f ()

let error format = Compat.error format

let print_flush (s:string) : unit = print s; flush ()
let printf_flush format = kprintf print_flush format

let check0 (x:bool) (s:string) : 'a = if not x then (print s; exit (-1))
let check (x:bool) format = kprintf (check0 x) format

let warn0 (s:string) : unit = print s
let warn format = kprintf warn0 format

let warn_if0 (x:bool) (s:string) : 'a = if not x then print s
let warn_if (x:bool) format = kprintf (warn_if0 x) format

let debug = false

let opt_list_show f s = if s=[] then "" else f s
let opt_space_show f s = if s=None then "" else " " ^ opt_show f s

let (==) : 'a -> 'a -> bool = Compat.obj_eq

(* Should be 'assert false', but a bug in F# causes 'assert false' 
to have unit return type instead of polymorphic. *)
let assert_false () : 'a = failwith "bottom"


(*--- Conventions
 
f,g,h - functions
a,b,c - elements
x,y,z,w - variables
s,t,u,v - sets

*)
