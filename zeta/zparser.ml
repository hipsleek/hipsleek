(**
 * Parser for a simple number theoretic
 * language
 *
 * @author Vu An Hoa
 *)

open Camlp4
open Ztoken
open Zutils
open Zsort
open Zterm
open Zlogic

module ZGram = Camlp4.PreCast.MakeGram(Zlexer.Make(Ztoken))

(* INPUT DATA STRUCTURE *)

type defn =
	(*| Axiom of term*)
	| Symbol of term * term list * term list option
	| Theorem of term

(* DEFINITION CONSTRUCTORS *)

(*let mkAxiom t = Axiom t*)

let mkSymbol l axms ind_hints = Symbol (l, axms, ind_hints)
	
let mkTheorem t = Theorem t

(* DEFINITION PRINTING *)

(*let string_of_defn tp d = match d with
	(*| Axiom t -> "<b>Axiom</b> \\(" ^ (tp t) ^ "\\)<br>"*)
	(*| Symbol (s, sl, t) -> 
		"<b>Definition</b> <i>" ^ s ^ "</i>" ^ (match t with
			| Some t1 -> " := \\(" ^ (tp t1) ^ "\\)<br>"
			| None -> "<br>")*)
	| Symbol (l, a, t) -> "<b>Definition</b> Let \\(" ^ (tp l) ^ "\\) be such that " ^ (String.concat "<br />" (List.map tp a))
	| Theorem t -> "<b>Theorem</b> \\(" ^ (tp t)  ^ "\\)<br>"*)

(* DEFINITION PROCESSING *)

let get_symbol_name d = match d with
	| Symbol (l, _, _) -> (match l with
		| Var (_, v) -> v
		| FunApp (GFunc, x) -> name_of_var (List.hd x)
		| _ -> failwith "Expected a var/fun app")
	| _ -> failwith "Expect symbol defn"

let get_defined_symbols defs =
	let res = List.map (fun d -> match d with
		| Symbol _ -> [get_symbol_name d]
		| _ -> []) defs in
		List.flatten res

let get_defn_term d = match d with
	(*| Axiom t*)
	| Theorem t -> [t]
	| Symbol (l, a, _) -> a

let get_all_terms defs =
	let res = List.map get_defn_term defs in
	let res = List.flatten res in
		res

let transform_term_in_defn ff d = 
	match d with
	(*| Axiom t -> Axiom (ff t)*)
		| Symbol (l, a, t) -> Symbol (ff l, List.map ff a, t) 
		| Theorem t -> Theorem (ff t)

let transform_term_in_defn_list ff defs =
	List.map (transform_term_in_defn ff) defs

let map_defn ff d = match d with
	(*| Axiom t -> ff t*)
	| Symbol (l, a, t) -> (ff l) :: (List.map ff a)
	| Theorem t -> [ff t]

let map_defn_list ff defs =
	List.map (map_defn ff) defs

let infer_sorts defs =
	(* collect & group symbols by name *)
	let vss = map_defn_list collect_vars defs in
	let vss = List.flatten vss in
	let vss = List.map (GList.group_elms eq_var) vss in
	(* generate local sorts unification constraints *)
	let gen_loc_unif_constr sym_class =
		(name_of_var (List.hd sym_class), List.map sort_of_term sym_class) in
	let vss = List.map (fun cs -> 
		List.map gen_loc_unif_constr cs) vss in
	(* extract global sorts unification constraints *)
	let globsyms = get_defined_symbols defs in
	(*let _ = print_endline ("Defined symbols : [" ^ (String.concat ", " globsyms) ^ "]") in*)
	let glob_constr = List.map (fun s ->
		List.flatten (List.map (fun cs -> 
			try List.assoc s cs
			with Not_found -> []) vss)) globsyms in
	let loc_constr = List.map (fun cs ->
		List.filter (fun c -> 
			not (List.mem (fst c) globsyms)) cs) vss in
	let locsyms, loc_constr = List.split (List.flatten loc_constr) in
	(*let _ = List.map2 (fun s c -> 
		print_endline ("Unification constraint for global symbol " ^ s ^ " : {" ^ 
			(String.concat "," (List.map string_of_sort c)) ^
		"}")) globsyms glob_constr in
	let _ = List.map (fun c -> 
		print_endline ("Local unification constraint : {" ^ 
			(String.concat "," (List.map string_of_sort c)) ^
		"}")) loc_constr in*)
	let constr = List.append glob_constr loc_constr in
	(* solve the unification *)
	let soln, _ = List.split (List.map unify_sort_list constr) in
	let soln = List.flatten soln in
	let soln, rem = subst_ground_sorts [] soln in
	let soln = List.sort (fun (x1,_) (x2,_) -> 
		match (x1, x2) with
			| (SWild i, SWild j) -> i - j
			| _ -> failwith "exception") soln in
	(*let _ = print_endline "Solution:" in
	let _ = List.map (fun (x, y) -> 
		print_endline ((string_of_sort x) ^ " --> " ^ (string_of_sort y))) soln in*)
	(* update symbols in all terms *)
	let defs = transform_term_in_defn_list 
		(fun t -> subst_sort_term soln t) defs in
	let sym_sort_table = Hashtbl.create 10 in
	let sym_sort = List.map (fun x -> List.fold_right subst_sort soln (List.hd x)) glob_constr in
	let _ = List.map2 (Hashtbl.add sym_sort_table) globsyms sym_sort in
	let sym_table = Hashtbl.create 10 in
	let _ = List.map (fun d -> match d with
		| Symbol (l, a, t) -> 
			let n = get_symbol_name d in
			let x = get_fun_app_arg l in
			let sinf = { name = n;
						symbol_sort = Hashtbl.find sym_sort_table n;
						axioms = (* Add forall to free variables *)
							(* List.map (fun t -> ) *) a;
						induction = match t with
							| Some t1 -> (* standardize inductions *)
								let stl = GList.mapi  
									(fun i y -> 
										let vi = Var (sort_of_term y, 
																	"$" ^ (string_of_int i)) in 
									(name_of_var y, vi)) x in
								List.map (subst stl) t1
							| None -> [];} in
				Hashtbl.add sym_table n sinf
		| _ -> ()) defs in
	(* universally quantified all the axioms *)
	let _ = Hashtbl.iter (fun x y -> 
		let axms = List.map (fun a ->
			let va = filter_defined_symbols sym_table (frv a) in
				FunApp (Forall, a :: va)) y.axioms in
		let _ = Hashtbl.remove sym_table x in
			Hashtbl.add sym_table x {y with axioms = axms}) 
		sym_table in
	(defs, sym_table)

let get_theorems_list defs = 
	let is_theorem d = match d with
		| Theorem t -> true
		| _ -> false in
	let thms = List.filter is_theorem defs in
	let get_theorem_struct d = match d with
		| Theorem t -> { thm = t; proved = false; }
		| _ -> failwith "Theorem expected!" in
	let thms = List.map get_theorem_struct thms in
		thms

(* GRAMMAR *)

let zeta = ZGram.Entry.mk "zeta";;

EXTEND ZGram GLOBAL : zeta;

zeta : [[ t = LIST0 definition -> t]];

definition : [[
		(*`AXIOM; a = formula; `DOT -> mkAxiom a
	|*) h = symbol_defn_header; `SUCH; `THAT; 
		a = LIST1 formula SEP `SEMICOLON; `DOT -> 
			mkSymbol (fst h) a (snd h)
	(*| h = symbol_defn_header; `DEFEQ; 
		t = formula; `DOT -> 
			mkSymbol (fst h) (snd h) (Some t)*)
	| `THEOREM; t = formula; `DOT -> mkTheorem t ]];

symbol_defn_header : [[
	`LET; a = OPT symbol_annotation; t = formula -> (t, a) ]];

formula : [
	"implication and iff" RIGHTA
	[ t1 = SELF; `RIGHTARROW ; t2 = SELF -> mkBinTerm Implies t1 t2
	| t1 = SELF; `LEFTRIGHTARROW ; t2 = SELF -> mkBinTerm Iff t1 t2]
| "disjunction" [ t1 = SELF; `OR; t2 = SELF -> mkBinTerm Or t1 t2]
| "conjunction" [ t1 = SELF; `AND; t2 = SELF -> mkBinTerm And t1 t2]
| "quantified formulas"
	[ `EXISTS; `OBRACE; qv = identifier_list; `CBRACE; t = SELF ->
			mkListTerm Exists (t::(List.map mkVar qv))
	| `FORALL; `OBRACE; qv = identifier_list; `CBRACE; t = SELF -> 
			mkListTerm Forall (t::(List.map mkVar qv)) ]
| "negation" [`NOT; t = SELF -> mkUnaryTerm Neg t]
| "standard equality/inequality"
	[ t1 = SELF; `EQ; t2 = SELF -> mkBinTerm Eq t1 t2
	| t1 = SELF; `GT; t2 = SELF -> mkBinTerm Gt t1 t2
	| t1 = SELF; `GTE; t2 = SELF -> mkBinTerm Ge t1 t2
	| t1 = SELF; `LT; t2 = SELF -> mkBinTerm Lt t1 t2
	| t1 = SELF; `LTE; t2 = SELF -> mkBinTerm Le t1 t2
	| t1 = SELF; `NEQ; t2 = SELF -> mkBinTerm Ne t1 t2]
| "additive"
	[ t1 = SELF; `PLUS; t2 = SELF -> mkBinTerm Add t1 t2
	| t1 = SELF; `MINUS; t2 = SELF -> mkBinTerm Sub t1 t2]
| "multiplicative"
	[ t1 = SELF; `STAR; t2 = SELF -> mkBinTerm Mul t1 t2
	| t1 = SELF; `DIV; t2 = SELF -> mkBinTerm Div t1 t2
	| t1 = SELF; `MOD; t2 = SELF -> mkBinTerm Mod t1 t2 ]
| "base"
	[ s = identifier -> mkVar s
	| `NUMERAL i -> Num i
	| `FALSE -> mkBot ()
	| `TRUE -> mkTop ()
	| f = identifier; `OPAREN; x = LIST0 SELF SEP `COMMA; `CPAREN ->
		mkListTerm GFunc (mkVar f::x)
	| f = identifier; `OSQUARE; x = LIST0 SELF SEP `COMMA; `CSQUARE ->
		mkListTerm GFunc (mkVar f::x)]
| [ `OPAREN; t=SELF; `CPAREN -> t ]];

identifier : [[ `IDENTIFIER s -> s ]];

identifier_list : [[ idlist = LIST0 identifier SEP `COMMA -> idlist ]];

symbol_annotation : [[ `OSQUARE; h = OPT induction_hints; `CSQUARE -> match h with None -> [] | Some t -> t]];

induction_hints : [[ `INDUCTION; p = LIST1 formula SEP `COMMA -> p ]];

END;;
		
(**
 * Parse an input stream and pre-process 
 * to obtain information on defined 
 * symbol and theorems.
 *
 * @return A hash table maps each symbol
 * to its information structure and a
 * list of theorems to be proved.
 *)
let parse n s =
	let defs = ZGram.parse zeta (PreCast.Loc.mk n) s in
	let defs, symtab = infer_sorts defs in
		(symtab, get_theorems_list defs)
