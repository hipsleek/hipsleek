(* jjar.ml - java jar (zip of class files) *)

type t

val load : string -> t
val cname_of : t -> Jplain.name -> Jtyped.cname
val cnames : t -> Jtyped.package -> Jtyped.id list -> Jtyped.cname list
val ifaces : t -> Jtyped.cname -> Jtyped.cname list
val field : t -> Jtyped.cname -> Jtyped.id -> Jtyped.fty
val methods : t -> Jtyped.cname -> Jtyped.id -> Jtyped.mty list
val super : t -> Jtyped.cname -> Jtyped.cname
val mods : t -> Jtyped.cname -> Jtyped.modifiers
val kind : t -> Jtyped.cname -> Jtyped.ckind
