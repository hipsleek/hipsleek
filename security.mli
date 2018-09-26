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

val string_of_lattice : lattice -> string

val current_lattice : lattice ref

val default_lattice : lattice
val make_lattice : Label.t list -> (Label.t * Label.t) list -> lattice
val is_valid_security_label : lattice -> Label.t -> bool
val get_top : lattice -> Label.t
val get_bottom : lattice -> Label.t
val get_representation : lattice -> Label.t -> int list
val representation_to_label : lattice -> int list -> Label.t
val least_upper_bound : lattice -> Label.t -> Label.t -> Label.t
val greatest_lower_bound : lattice -> Label.t -> Label.t -> Label.t
val lattice_size : lattice -> int
val representation_tuple_length : lattice -> int
