open Camlp4.PreCast

type zeta_token =
	| IDENTIFIER of string
	| NUMERAL of int
	| LET | INDUCTION | DEFEQ | AXIOM | THEOREM | SUCH | THAT
	| EXISTS | FORALL | FALSE | TRUE | NOT 
	| AND | OR | RIGHTARROW | LEFTRIGHTARROW
	| PLUS | MINUS | STAR | DIV | MOD
	| EQ | GT | GTE | LT | LTE | NEQ 
	| OPAREN | CPAREN | OSQUARE | CSQUARE
	| OBRACE | CBRACE 
	| COLON | COMMA | SEMICOLON | DOT | EOF

module type ZTokenS = Camlp4.Sig.Token with type t = zeta_token
  
module Ztoken = struct
  open Format
  
	module Loc = Camlp4.PreCast.Loc
	
  type t = zeta_token
  type token = t

  let sf = Printf.sprintf

  let to_string k = match k with 
		| IDENTIFIER s -> s
		| _ -> ""
    
  let print ppf x = pp_print_string ppf (to_string x)

  let match_keyword kwd _ = false 

  let extract_string t = match t with
		| IDENTIFIER s -> s
		| NUMERAL i -> string_of_int i
		| _ -> ""
    
  module Error = struct
    type t = string
    exception E of string
    let print = pp_print_string
    let to_string x = x
  end

  module Filter = struct
    type token_filter = (t, Loc.t) Camlp4.Sig.stream_filter

    type t =
      { is_kwd : string -> bool;
        mutable filter : token_filter }

    let mk is_kwd =
      { is_kwd = is_kwd;
        filter = (fun s -> s) }

    let filter x = fun strm -> x.filter strm

    let define_filter x f = x.filter <- f x.filter

    let keyword_added _ _ _ = ()
    let keyword_removed _ _ = ()
  end

end

module Error = Camlp4.Struct.EmptyError
