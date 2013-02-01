(* stringx.ml - string (immutable and extended)  -*- caml -*- *)

open Std
module C = Charx
module A = Arrayx
module L = Listx

let make : int -> string = Compat.string_create
let size : string -> int = String.length
let get : string -> int -> char = String.get
let getx : string -> int -> char = Compat.string_unsafe_get
let set : string -> int -> char -> string = Compat.string_set


let check (caller:string) (s:string) (offset:int) (count:int) : unit =
  if offset<0 then fail "Stringx.%s: offset<0: %d" caller offset
  else if size s<offset+count then 
    fail "Stringx.%s: size<offset+count: %d, %d, %d" 
      caller (size s) offset count
  else ()

let of_array (s:char array) : string = Compat.string_of_array s

let to_array (s:string) : char array =
  let n = size s in
  let l = Arrayx.make n '\000' in
  for i = 0 to n - 1 do Arrayx.setx l i (getx s i) done; l

(* Assumption: 0 <= offset <= size s - count. *)
let subx (s:string) (offset:int) (count:int) : string =
  of_array (A.subx (to_array s) offset count)

let sub (s:string) (offset:int) (count:int) : string =
  check "sub" s offset count;
  subx s offset count

let suby (s:string) (offset:int) (count:int) : string =
  let i = cram offset 0 (size s) in
  let n = cram count 0 (size s - i) in
  subx s i n

(* TODO consistent function naming for index, upto, count, offset *)

(* from index i (inclusive) to index j (exlcusive) *)
let subj s i j = subx s i (j - i)

let subi s i = subx s i (size s - i)

let dup (s:string) : string = subx s 0 (size s)

let head (s:string) : char = check "head" s 0 1; getx s 0
let tail (s:string) : string = sub s 1 (size s - 1)
let last (s:string) : char = check "tail" s 0 1; getx s (size s - 1)

let cut_last (n:int) (s:string) : string = sub s 0 (size s - n - 1)

let map (f:char -> char) (s:string) : string =
  of_array (A.map f (to_array s))

let itern (f:char -> unit) (count:int) (s:string) : unit =
  let n = min (count-1) (size s-1) in
  for i=0 to n do f (getx s i) done

let iter (f:char -> unit) (s:string) : unit = itern f max_int s

let rev (s:string) : string = of_array (A.rev (to_array s))

let join (s1:string) (s2:string) : string =
  of_array (A.cat2 (to_array s1) (to_array s2))

let cat0 (s:string list) : string =
  of_array (A.cat_list (L.map to_array s))

let cat (sep:string) (s:string list) : string =
  cat0 (L.separate sep s)

let catz (s:string list) : string = cat " " s
let cat1 (s:string list) : string = cat "\n" s
let cat2 (s:string list) : string = cat "\n\n" s

let suffix_with (sep:string) (s:string list) : string =
  cat0 (L.suffix sep s)

let rec alli (f:char -> bool) (s:string) (i:int) : bool =
  i >= size s || (f (getx s i) && alli f s (i+1))

let rec somei (f:char -> bool) (s:string) (i:int) : bool =
  i < size s && (f (getx s i) || somei f s (i+1))

let rec memi (a:char) (s:string) (i:int) : bool =
  i < size s && ((a = getx s i) || memi a s (i+1))

let all f s = alli f s 0
let some f s = somei f s 0
let mem (a:char) (s:string) : bool = memi a s 0

let lower (s:string) : string = map C.lower s
let upper (s:string) : string = map C.upper s

let capitalize (s:string) : string = set s 0 (C.upper (get s 0))

let is_lower (s:string) : bool = lower s = s
let is_upper (s:string) : bool = upper s = s
let is_capital (s:string) : bool = capitalize s = s

(* todo: perl regular-expression syntax class *)

let is_alpha : string -> bool = all C.is_alpha
let is_num : string -> bool = all C.is_num

let rec find_in (s:string) (offset:int) (limit:int) (c:char) : int = 
  if offset >= limit then -1
  else if getx s offset = c then offset 
  else find_in s (offset+1) limit c

let find (s:string) (c:char) : int = find_in s 0 (size s) c

(* find a char from reverse *)
let rec rev_find_from (i:int) (c:char) (s:string) : int = 
  if i<0 then raise Not_found
  else if getx s i = c then i 
  else rev_find_from (i-1) c s

let rev_find (c:char) (s:string) : int = rev_find_from (size s - 1) c s

let rec cmpj (s1:string) (i1:int) (j1:int)
  (s2:string) (i2:int) (j2:int) : bool =
  i1 >= j1 || i2 >= j2 || 
  (getx s1 i1 = getx s2 i2 && cmpj s1 (i1+1) j1 s2 (i2+1) j2)

let cmpi s1 i1 s2 i2 = cmpj s1 i1 (size s1) s2 i2 (size s2)

let rec aligni (s1:string) (s2:string) (i:int) : int =
  if i >= size s2 || cmpi s1 0 s2 i then i
  else aligni s1 s2 (i+1)

let align s1 s2 = aligni s1 s2 0

let is_subset (s1:string) (s2:string) : bool = align s1 s2 <> -1  
let of_char : char -> string = C.show
let of_int : int -> string = string_of_int
let of_bool : bool -> string = string_of_bool

let to_float : string -> float = float_of_string
let to_bool : string -> bool = bool_of_string
let to_int : string -> int = int_of_string
let to_char : string -> char = C.read

let of_list (l:char list) : string = of_array (A.of_list l)

(* Assumption: 0 <= offset *)
let rec to_list_from (s:string) (offset:int) : char list =
  if offset >= size s then []
  else getx s offset :: to_list_from s (offset+1)

let to_list (s:string) : char list = to_list_from s 0

let map_list (f:char -> 'a) (s:string) : 'a list = L.map f (to_list s)

let rec readi (sep:string) (s:string) (i:int) : string list =
  if i >= size s then [] else
  let j = aligni sep s i in
  if j = i + size sep - 1 then readi sep s (j + size sep)
  else subj s i j :: readi sep s (j + size sep)

(* tokenize *)
let read (sep:char) (s:string) : string list = readi (of_char sep) s 0

let insert (i:int) (a:char) (s:string) : string = 
  of_list (L.insert i a (to_list s))

let mapc (f:char -> string) (s:string) : string =
  cat0 (map_list f s)

let show = mapc C.code
let showf = mapc C.codef

let mapc_with (f:char -> string) (sep:string) (s:string) : string =
  cat sep (map_list f s)

let code (s:string) : string = "\"" ^ show s ^ "\""
let codef (s:string) : string = "\"" ^ showf s ^ "\""

let fprint : out_channel -> string -> unit = output_string

let fcode (f:out_channel) (x:string) : unit = fprint f (code x)

let to_hex (f:out_channel) (s:string) : unit =
  for i = 0 to size s - 1 do
    if i mod 20 = 0 then output_string f "\\\n";
    output_string f "\\x";
    output_string f (C.to_hex s.[i]);
  done

let to_oct (f:out_channel) (s:string) : unit =
  for i = 0 to size s - 1 do
    if i mod 20 = 0 then output_string f "\\\n";
    output_string f "\\";
    output_string f (C.to_oct s.[i]);
  done

let to_dec (f:out_channel) (s:string) : unit =
  for i = 0 to size s - 1 do
(*    if i mod 20 = 0 then output_string f "\\\n"; *)
    output_string f "\\";
    output_string f (C.to_dec s.[i]);
  done

let repeat (x:int) (s:string) : string = cat0 (L.make s x)

let if_null (s1:string) (s2:string) : string = if s2="" then s1 else s2

let if_cat (x:bool) (s1:string) (s2:string) = if x then s1 ^ s2 else s2

(* substitute *)
let subst (s:string) (x1:char) (x2:char) : string =
  map (fun x -> if x=x1 then x2 else x) s

(* optimize *)
let rec upto (a:char) (s:string) = of_list (L.upto a (to_list s))

(* is s1 a prfix of s2 *)
let is_prefix (s1:string) (s2:string) : bool =
  s1 = s2 ||
  (size s1 <= size s2 && s1 = subj s2 0 (size s1))

(* is s1 a suffix of s2 *)
let is_suffix (s1:string) (s2:string) : bool =
  s1 = s2 ||
  let n = size s2 in
  (size s1 <= size s2 && s1 = subj s2 (n - size s1) n)

(* trim head by m and tail by n *)
let trim (m:int) (n:int) (s:string) : string = 
  of_array (A.trim m n (to_array s))

(* skip first characters *)
let skip (n:int) (s:string) : string = sub s n (size s - n)
