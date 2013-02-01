
type 'a t
val add : 'a -> 'a t -> 'a t
val empty : 'a t
val is_empty : 'a t -> bool
val is_nonempty : 'a t -> bool
val mem : 'a -> 'a t -> bool
val foldr : ('a -> 'b -> 'b) -> 'b -> 'a t -> 'b
val union : 'a t -> 'a t -> 'a t
val head : 'a t -> 'a
val tail : 'a t -> 'a t
val single : 'a -> 'a t
val minus : 'a t -> 'a t -> 'a t
val del : 'a -> 'a t -> 'a t
val some : ('a -> bool) -> 'a t -> bool
val iter : ('a -> unit) -> 'a t -> unit
val all : ('a -> bool) -> 'a t -> bool
val size : 'a t -> int
val subset : 'a t -> 'a t -> bool
val of_list : 'a list -> 'a t
val of_set : 'a list -> 'a t
val foldl : ('a t -> 'a -> 'a t) -> 'a t -> 'a t -> 'a t
val union_list : 'a t list -> 'a t
val to_list : 'a t -> 'a list
val to_list_list : 'a t t -> 'a t list
val of_list_array : 'a list array -> 'a t
val map_list : ('a -> 'b) -> 'a t -> 'b list
val list_map : ('a -> 'b) -> 'a list -> 'b t
val map : ('a -> 'b) -> 'a t -> 'b t
val mapc : ('a -> 'b t) -> 'a t -> 'b t
val imapc : ('a -> int t) -> 'a t -> int t
val show : string -> ('a -> string) -> 'a t -> string
val showz : ('a -> string) -> 'a t -> string
val show0 : ('a -> string) -> 'a t -> string
val show1 : ('a -> string) -> 'a t -> string
val show2 : ('a -> string) -> 'a t -> string
val showxz : 'a t -> string
val showx : string -> 'a t -> string
val induction : (unit -> 'a) -> ('b -> 'b t -> 'a) -> 'b t -> 'a
val take : ('a -> bool) -> 'a t -> 'a t
val fixpoint : ('a -> 'b -> 'a * 'b t) -> 'a -> 'b t -> 'a
val worklist : ('a -> 'a t) -> 'a t -> unit
val dfs : ('a -> 'a t) -> 'a t -> unit
val compress : 'a option t -> 'a t
val collect : ('a -> 'b option) -> 'a t -> 'b t
val index : 'a t -> (int * 'a) t
val rindex : 'a t -> ('a * int) t
val interval : int -> int -> int t
val count : ('a -> bool) -> 'a t -> int
val domain : ('a * 'b) t -> 'a t
val range : ('a * 'b) t -> 'b t
val test : 'a t -> unit
val of_array : 'a array -> 'a t
val to_array : 'a t -> 'a array
val fcode : (out_channel -> 'a -> unit) -> out_channel -> 'a t -> unit
val of_list_set : 'a t list -> 'a t
val list_mapc : ('a -> 'b t) -> 'a list -> 'b t
val last : 'a t -> 'a
val printz : ('a -> unit) -> 'a t -> unit
val print : string -> ('a -> unit) -> 'a t -> unit
val printxz : 'a t -> unit
val printx : string -> 'a t -> unit
val get : 'a t -> int -> 'a
val check_subset : 'a t -> 'a t -> unit
val check_eq : 'a t -> 'a t -> unit
val check_mem : 'a -> 'a t -> unit
val array_add : 'a t array -> int -> 'a -> unit
val array_union : 'a t array -> int -> 'a t -> unit
val array_index : bool array -> int t
val closure : int t array -> unit
val fprintf : (out_channel -> 'a -> unit) -> out_channel -> 'a t -> unit
val find : ('a -> bool) -> 'a t -> 'a option
val restrict1 : 'a -> ('a * 'b) t -> 'b t
val restrict2 : 'b -> ('a * 'b) t -> 'a t
val intersect : 'a t -> 'a t -> 'a t
val disjoint : 'a t -> 'a t -> bool
