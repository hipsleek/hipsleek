type t

val make : string -> t
val anon : unit -> t
val primed : string -> t (* TODO check what primed variable to, to give this a more descriptive name *)

val is_primed : t -> bool
val is_anon : t -> bool
val to_string : t -> string

val to_sleek_ident : t -> string * Hipsleek_common.VarGen.primed
val of_sleek_ident : string * Hipsleek_common.VarGen.primed -> t
val of_sleek_spec_var : Hipsleek_common.Cpure.spec_var -> t
