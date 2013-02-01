(* unzip.mli - unpack zip/jar archives *)

type zip
type entry

val read : zip -> entry -> string 
val load : string -> zip 
val find : zip -> string -> entry       (* Raise Not_found. *)
val name : entry -> string
val all : zip -> entry list 
