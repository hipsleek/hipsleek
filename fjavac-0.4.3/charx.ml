(* charx.ml - character (extended) *)

let is_print : char -> bool = Compat.char_is_print
let to_int : char -> int = Char.code
let of_int : int -> char = Char.chr

let lower (c:char) : char =
  if ('A' <= c && c <= 'Z')
  || ('\192' <= c && c <= '\214')
  || ('\216' <= c && c <= '\222')
  then of_int (to_int c + 32) else c

let upper (c:char) : char =
  if ('a' <= c && c <= 'z')
  || ('\224' <= c && c <= '\244')
  || ('\246' <= c && c <= '\252')
  then of_int (to_int c - 32) else c

let is_upper (c:char) : bool = ('A' <= c && c <= 'Z')
let is_lower (c:char) : bool = ('a' <= c && c <= 'z')

let is_alpha (c:char) : bool =
  let i = to_int c in
  (to_int 'A' <= i && i <= to_int 'Z')
  || (to_int 'a' <= i && i <= to_int 'z')

let is_num (c:char) : bool =
  let i = to_int c in
  to_int '0' <= i && i <= to_int '9'

let show : char -> string = String.make 1
let read (s:string) : char = s.[0]

let backslash (c:char) : string = Std.showf "\\%03d" (to_int c)

let to_hex (c:char) : string = 
  let a = [|'0';'1';'2';'3';'4';'5';'6';'7';'8';'9';'a';'b';'c';'d';'e';'f'|] in
  let i = to_int c in
  let c0 = a.(i lsr 4) in
  let c1 = a.(i land 0xf) in
  Compat.string_of_array [|c0; c1|]

let to_oct (c:char) : string = 
  let a = [|'0';'1';'2';'3';'4';'5';'6';'7'|] in
  let i = to_int c in
  let c0 = a.(i lsr 6 land 0x7) in
  let c1 = a.(i lsr 3 land 0x7) in
  let c2 = a.(i land 0x7) in
  Compat.string_of_array [|c0; c1; c2|]

let to_dec (c:char) : string = 
  let a = [|'0';'1';'2';'3';'4';'5';'6';'7';'8';'9'|] in
  let i = to_int c in
  let c0 = a.(i / 100) in
  let c1 = a.(i mod 100 / 10) in
  let c2 = a.(i mod 10) in
  Compat.string_of_array [|c0; c1; c2|]

let code : char -> string = function
  | '\'' -> "\\'" (* single quote *)
  | '"' -> "\\\"" (* double quote *)
  | '\\' -> "\\\\" (* backslash *)
  | '\b' -> "\\b" (* backspace *)
  | '\n' -> "\\n" (* newline *)
  | '\r' -> "\\r" (* return *)
  | '\t' -> "\\t" (* tabulation *)
  | c when is_print c -> show c
  | c -> backslash c

(* code for format string *)
let codef : char -> string = function
  | '%' -> "%%" (* percent *)
  | c -> code c
