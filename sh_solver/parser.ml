open Camlp4
open Camlp4.PreCast
 
module Ts = Tree_shares.Ts
module Sv = 
  struct
	type t=string
	let cnt = ref 1
	let eq v1 v2 = (String.compare v1 v2) = 0
    let string_of v1 = v1
	let rename _ s = s
    let get_name v = v
	let var_of v = v
    let fresh_var _ = cnt:=cnt+1; "__ts_fv_"^(string_of_int !cnt)    
end

module Solver = Share_prover.Dfrac_s_solver(Ts)(Sv)(Ss)

module Eqs = 
	struct 
	type var = Sv.t
	type const = Ts.stree
	type pcvar = Solver.frac_perm
	type eq = Solver.eq
	type eq_syst = Solver.eq_syst
	let mkVar = Sv.var_of
	let mkEq v1 v2 v3 = (v1,v2,v3)
	let mkEqS l1 l2 l3 = (l1,l2,l3)
	let mkcFull = Ts.full
	let mkcEmpty = Ts.empty
	let mkcNode = Ts.mkNode 
	let mkpcCnst c = Solver.Cperm c
	let mkpcVar v = Solver.Vperm v
end
	
type sp_token =
  | IDENTIFIER    of string
  | EOF 
  | EQ 
  | COMMA
  | STAR
  | OPAREN
  | CPAREN
  | HASH
  | DOT
  
module type SPTokenS = Camlp4.Sig.Token with type t = sp_token
  
module Token = struct
  open Format
  module Loc = Loc
  type t = sp_token
  type token = t
  let sf = Printf.sprintf
  let to_string k = match k with | EOF -> "" | EQ ->"="  | COMMA ->"," | STAR -> "*" | CPAREN->")"  | OPAREN->"("  | DOT ->"." |HASH -> "#" | IDENTIFIER s -> s	
  let print ppf x = pp_print_string ppf (to_string x)
  let match_keyword kwd _ = false     
  let extract_string t = match t with | IDENTIFIER s -> s | _ -> ""    
    
  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter
    type t = { is_kwd : string -> bool; mutable filter : token_filter }
    let mk is_kwd = { is_kwd = is_kwd; filter = (fun s -> s) }
    let filter x = fun strm -> x.filter strm
    let define_filter x f = x.filter <- f x.filter
    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end
end
module Error = Camlp4.Struct.EmptyError


module SPGram = Camlp4.Struct.Grammar.Static.Make(Lexer.Make(Token))
type command = 
	| Sat of Eqs.eq_syst
	| Imply of Eqs.eq_syst * Eqs.eq_syst
			
let eq_systs = SPGram.Entry.mk "eq_systs" 
			
EXTEND SPGram
		GLOBAL: eq_systs;

		eq_systs: [[t = eq_syst ; `EOF -> Sat t
				  |t1 = eq_syst ; t2 = eq_syst ;`EOF -> Imply (t1,t2) ]];
		
		eq_syst:[[ exv = var_list; `DOT ; nzv=var_list ; `DOT ; eqs = eq_list ; `DOT -> EQS.mkEqS exv nzv eqs ]];
  
		var : [[`IDENTIFIER s -> EQS.mkVar s]];
		
		var_list:[[ t= LIST0 var SEP `COMMA -> t]];

		eq_list:[[t=LIST0 eq SEP `COMMA -> t]];  
   
		eq:[[v1=vc; `STAR; v2=vc; `EQ ; v3= vc -> EQS.mkEq v1 v2 v3 ]];

		vc:[[c = shc -> EQS.mkpcCnst c
			|v = var -> EQS.mkpcVar v]];
			
		shc:[[`HASH -> EQS.mkcFull
			  | `OPAREN; l=shc; `COMMA; `CPAREN -> Ts.mkNode l EQS.mkcEmpty
			  | `OPAREN; `COMMA; r=shc; `CPAREN -> Ts.mkNode EQS.mkcEmpty l
			  | `OPAREN; l=shc; `COMMA; r=shc; `CPAREN -> EQS.mkcNode l r ]];
		END;;
		
 let parse_eq_syst n s = SPGram.parse eq_systs (PreCast.Loc.mk n) s

  