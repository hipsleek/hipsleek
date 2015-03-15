open Debug

let build s i = "**"^s^":"^(string_of_int i)^":";;

#define debug(f,s) let s1 = build __FILE__ __LINE__ in \
       Debug.binfo_hprint (fun x -> s1^(f x)) s VarGen.no_pos

(* let s1 = build __FILE__ __LINE__ in \
       Debug.binfo_hprint (fun x -> s1^(f x)) s VarGen.no_pos
*)
