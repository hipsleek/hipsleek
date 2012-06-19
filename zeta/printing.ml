(**
 * Printing of terms and formulas
 *
 * @author Vu An Hoa
 *)

module type BasePrinter = sig
	
	val print_domain : Domain.domain -> string
	
	val print_func : (int -> string) -> Term.func -> string
	
	val print_int : int -> string
	
	val top : string
	
	val bot : string
	
	val newline : string
	
	val term_start : string
	
	val term_end : string 
	
end

module StringBasePrinter : BasePrinter = struct
	
	open Domain
	open Term
	
	let rec print_domain d = match d with
		| SBool -> "2"
		| SInt -> "Z"
		| SWild i -> 
			"X_" ^ (string_of_int i)
		| SMap d -> 
			let dom = String.concat "x" (List.map print_domain (List.tl d)) in
			let co_dom = print_domain (List.hd d) in
				dom ^ "->" ^ co_dom
	
	let print_func print_symbol f = match f with
		| Add -> "+"
		| Sub -> "-"
		| Mul -> "*" 
		| Div -> "/"
		| Mod -> "mod"
		| Eq -> "="
		| Ne -> "!="
		| Lt -> "<" 
		| Le -> "<="
(*		| Gt -> ">" *)
(*		| Ge -> ">="*)
		| And -> " /\\ " 
		| Or -> " \\/ " 
		| Neg -> "~" 
		| Implies -> "->" 
		| Iff -> "<->" 
		| Exists -> "E" 
		| Forall -> "A"
		| GF i -> print_symbol i
	
	let print_int = string_of_int
	
	let top = "t"
	
	let bot = "f"
	
	let newline = "\n"
	
	let term_start = ""
	
	let term_end = ""
	
end

module TexBasePrinter : BasePrinter = struct
	
	open Domain
	open Term
	
	let rec print_domain d = match d with
		| SBool -> 
			"\\mathbb{B}"
		| SInt -> 
			"\\mathbb{Z}"
		| SWild i -> 
			"\\mathcal{X}_{" ^ (string_of_int i) ^ "}" 
		| SMap d ->
			let dom = String.concat "\\times" (List.map print_domain (List.tl d)) in
			let co_dom = print_domain (List.hd d) in
				dom ^ " \\mapsto " ^ co_dom
	
	let print_func print_symbol f = match f with
		| Add -> "+"
		| Sub -> "-"
		| Mul -> "\\times"
		| Div -> "\\div" 
		| Mod -> "\\bmod"
		| Eq -> "=" 
		| Ne -> "\\not="
		| Lt -> "<" 
		| Le -> "\\leq"
(*		| Gt -> ">"    *)
(*		| Ge -> "\\geq"*)
		| And -> "\\land"
		| Or -> "\\lor" 
		| Neg -> "\\neg"
		| Implies -> "\\rightarrow"
		| Iff -> "\\leftrightarrow"
		| Exists -> "\\exists" 
		| Forall -> "\\forall"
		| GF i -> print_symbol i

	let print_int i = "\\underline{\\mathsf{" ^ (string_of_int i) ^ "}}"

	let top = "\\top"
	
	let bot = "\\bot"
	
	let newline = "\n<br /><br /><br />\n"
	
	let term_start = "\\("
	
	let term_end = "\\)"
	
end

(*

module type VarPrinter = sig
	
	val print_var : int -> string
	
end

module RawVarPrinter : VarPrinter = struct
	
	let print_var i =
		if (i < 0) then
			"c_{" ^ (string_of_int (-i)) ^ "}"
		else
			"X_{" ^ (string_of_int i) ^ "}"
	
end

module StringVarPrinter : VarPrinter = struct
	
	let int_string_map : (int, string) Hashtbl.t = Hashtbl.create 10 
	
	let print_var i =
		try
			Hashtbl.find int_string_map i
		with
			| Not_found -> 
				RawVarPrinter.print_var i
	
end

*)

module Printer (BP : BasePrinter) = struct
	
	open Term
	open Theory

	let print_symbol i =
		if (i < 0) then
			"C_{" ^ (string_of_int (-i)) ^ "}"
		else
			"v_{" ^ (string_of_int i) ^ "}"
			
	let precedence_of f = match f with
		| Implies
		| Iff -> 1
		| Or -> 2
		| And -> 3
		| Exists
		| Forall -> 4
		| Neg -> 5
		| Eq
		| Ne
(*		| Gt *)
(*		| Ge *)
		| Lt
		| Le -> 7
		| Add
		| Sub -> 8
		| Mul
		| Div
		| Mod -> 9
(*		| Top      *)
(*		| Bot -> 10*)
		| GF _ -> 10

	let rec print_term_helper p t  = match t with
		| Top -> BP.top
		| Bot -> BP.bot
		| Num i -> BP.print_int i
		(*| Var (s, v) -> pr_var s v*)
		| Fx (f, x) ->
			let pf = precedence_of f in
			let xp = match f with | GF _ -> 0 | _ -> pf in
			let sx = List.map (print_term_helper xp) x in
			let sf = BP.print_func print_symbol f in
			let e = match f with
				| Exists
				| Forall ->
					let qv = String.concat "," (List.tl sx) in
						sf ^ " " ^ qv ^ " : " ^ (List.hd sx)
				| GF _ ->
					let args = String.concat "," ((*List.tl*) sx) in
					sf (*(List.hd sx)*) ^ 
					(match sx with
						| [] -> ""
						| _ -> "[" ^ args ^ "]")
				| Neg ->
					sf ^ " " ^ (List.hd sx)
				| _ -> (* other pre-defined infix operators *)
					if (f = Sub && List.length sx = 1) then
						sf ^ (List.hd sx)
					else
						String.concat (" " ^ sf ^ " ") sx in
			if (pf >= p) then
				e
			else
				"(" ^ e ^ ")"
	
	let print_term t = print_term_helper 0 t
	
	let print_definition d = ""
	
	let print_proof p = ""
	
	let print_theorem t = ""
	
	let print_theory c =
		let print_symbol s = "<b>Definition:</b> " ^ s.symbol_name ^ " ; id = " ^ (string_of_int s.symbol_id) ^ BP.newline in
		let syms = String.concat "" (List.map print_symbol c.def_symbols) in
		let print_thm t = "<b>Theorem:</b> " ^ BP.term_start ^ (print_term t.theorem_content) ^ BP.term_end ^ BP.newline in
		let thms = String.concat "" (List.map print_thm c.theorems) in
			syms ^ thms
	
end