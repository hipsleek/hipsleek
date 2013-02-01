(* compat.ml - compatibility for OCaml compiler *)

let list_merge = List.merge
external char_is_print : char -> bool = "caml_is_printable"

let int_show = string_of_int
let float_show = string_of_float

let rec list_initi (i:int) (n:int) (f:int -> 'a) : 'a list =
  if i>=n then [] else
  (f i) :: (list_initi (i+1) n f)

let list_init (n:int) (f:int -> 'a) : 'a list = list_initi 0 n f

let rec list_show (sep:string) (f:'a -> string) : 'a list -> string = function
  | [] -> ""
  | [x] -> f x
  | x::xs -> f x ^ sep ^ list_show sep f xs

let rec block_show (x:Obj.t) : string =
  let s = list_init (Obj.size x) (fun i -> Obj.field x i) in
  list_show " " obj_show s

and block_show2 (x:Obj.t) : string =
  let s = list_init (Obj.size x) (fun i -> Obj.field x i) in
  "(" ^ int_show (Obj.tag x) ^ " " ^ (list_show " " obj_show s) ^ ")"

and obj_show (x:Obj.t) : string =
  let y = Obj.obj x in
  let tag = Obj.tag x in
  if tag = Obj.string_tag then y else
  if tag = Obj.int_tag then int_show y else
  if tag = Obj.double_tag then float_show y else
  block_show x

let show (x:'a) : string = obj_show (Obj.repr x)
let to_tag (a:'a) : int = (Obj.tag (Obj.repr a))
let to_int (a:'a) : int = Obj.magic a


external hash_param : int -> int -> 'a -> int = "caml_hash_univ_param" "noalloc"
let hash x = hash_param 10 100 x

let max_array_length : int = Sys.max_array_length

let obj_eq : 'a -> 'a -> bool = (==)

let lex_start (x:Lexing.lexbuf) : Lexing.position = x.Lexing.lex_start_p
let lex_get (x:Lexing.lexbuf) : Lexing.position = x.Lexing.lex_curr_p
let lex_set (x:Lexing.lexbuf) (p:Lexing.position) : unit = 
  x.Lexing.lex_curr_p <- p

let string_set (s:string) (i:int) (c:char) : string = 
  let s2 = String.copy s in s2.[i] <- c; s2

let string_of_array (s:char array) : string = 
  let n = Array.length s in
  let s2 = String.create n in
  for i = 0 to n - 1 do String.unsafe_set s2 i (Array.unsafe_get s i) done; s2

let string_unsafe_get (s:string) (i:int) : 'a = String.unsafe_get s i
let array_unsafe_get (s:'a array) (i:int) : 'a = Array.unsafe_get s i
let array_unsafe_set (s:'a array) (i:int) (a:'a) : unit = Array.unsafe_set s i a
let string_create (i:int) : string = String.create i

let rec realpath s =
  match (Unix.lstat s).Unix.st_kind with
  | Unix.S_LNK -> realpath (Unix.readlink s)
  | _ -> s

let marshal_to_channel c x = Marshal.to_channel c x []
let marshal_from_channel c = Marshal.from_channel c

let error0 (s:string) : 'a = print_endline s; exit (-1)
let kprintf f fmt = Printf.ksprintf f fmt (* F# bug: omission *)
let error format = kprintf error0 format

let to_binary (x:'a) : string = Marshal.to_string x []
let of_binary (x:string) : 'a = Marshal.from_string x 0

let channel_to_string (c:in_channel) : string =
  let n = in_channel_length c in
  let s = String.create n in
  really_input c s 0 n; s
