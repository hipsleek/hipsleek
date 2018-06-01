module Label :
  sig
    type t
    val compare : 'a -> 'a -> int
    val equal : 'a -> 'a -> bool
    val hash : 'a -> int
    val to_string : t -> string
    val make : string -> t
  end

type lattice

val default_lattice : lattice
val make_lattice : Label.t list -> (Label.t * Label.t) list -> lattice
val is_valid_security_label : lattice -> Label.t -> bool
val get_top : lattice -> Label.t
val get_bottom : lattice -> Label.t
val least_upper_bound : lattice -> Label.t -> Label.t -> Label.t
val greatest_lower_bound : lattice -> Label.t -> Label.t -> Label.t
