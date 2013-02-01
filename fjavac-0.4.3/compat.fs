(* compat.fs - compatibility with F# compiler *)

let rec list_merge cmp a b = 
  match a,b with 
  | [], b -> b
  | a, [] -> a
  | x::a', y::b' -> 
    if cmp x y > 0 
    then y::list_merge cmp a  b' 
    else x::list_merge cmp a' b  

let char_is_print (c:char) : bool =
 let i = Char.code c in 
 i>=32 && i<=126

let string_of_array (s:char array) : string = 
  new System.String (Microsoft.FSharp.Compatibility.CompatArray.of_array s)

let string_set (s:string) (i:int) (c:char) : string =
  let mutable s2 = s.ToCharArray () in
  Microsoft.FSharp.Compatibility.CompatArray.set s2 i c;
  new System.String (s2)

let obj_eq = Obj.eq

let show : 'a -> string = any_to_string

let max_array_length = max_int

let lex_get : Lexing.lexbuf -> Lexing.position = Lexing.lexbuf_curr_p
let lex_set : Lexing.lexbuf -> Lexing.position -> unit = Lexing.lexbuf_set_curr_p
let lex_start : Lexing.lexbuf -> Lexing.position = Lexing.lexeme_start_p

let string_unsafe_get (s:string) (i:int) : 'a = String.get s i
let array_unsafe_get (s:'a array) (i:int) : 'a = Array.get s i
let array_unsafe_set (s:'a array) (i:int) (a:'a) : unit = Array.set s i a

let string_create (n:int) : string = String.make n '\000'

let hash = Pervasives.hash

let realpath s = Mono.Unix.UnixPath.GetRealPath s

let error0 (s:string) : 'a = print s; exit (-1)
let error format = Printf.failwithf format (* F# bug: polymorphic *)

let to_binary (x:'a) : string = 
  let ms = new System.IO.MemoryStream () in
  let sw = new System.IO.StreamWriter (ms) in
  output_value (stream_writer_to_out_channel sw) x;
  Bytearray.ascii_to_string (ms.ToArray ())

let of_binary (x:string) : 'a = 
  let ms = new System.IO.MemoryStream () in
  let a = Bytearray.string_to_ascii x in
  ms.Write (a, 0, Bytearray.length a);
  ms.Position <- 0L;
  let sw = new System.IO.StreamReader (ms) in
  input_value (stream_reader_to_in_channel sw)

let marshal_to_channel c x = output_value c x
let marshal_from_channel c = input_value c

let channel_to_string (c:in_channel) : string =
  let n = in_channel_length c in
  let s = Bytearray.make n in
  really_input c s 0 n;
  Bytearray.ascii_to_string s
