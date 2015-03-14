open VarGen
open Camlp4.PreCast
open Cformula
open Cpure
open Globals
open Lexing
open Gen

module H = Hashtbl

let loc = no_pos;;

(*let stab = ref (H.create 103);;*)

let expression = Gram.Entry.mk "expression";;

let summaries = Gram.Entry.mk "summaries";;

let summary = Gram.Entry.mk "summary";;

let fml = Gram.Entry.mk "fml";;

let pred = Gram.Entry.mk "pred";;

let preddef = Gram.Entry.mk "preddef";;

let ptr = Gram.Entry.mk "ptr";;

let lbl = Gram.Entry.mk "lbl";;

let id = Gram.Entry.mk "id";;


let gen_conj x y = normalize 1 x y loc;;

let parse_lbl x = match x with
  | None -> ("",-1)
  | Some (1,n) -> (!domain_name,int_of_string n)
  | Some _ -> ("",-1) ;;


EXTEND Gram
GLOBAL: expression summaries summary fml pred preddef ptr lbl id;
  expression:
  [ "expression" LEFTA
    [ x = LIST1 summaries -> x ]
  ];

  summaries:
  [ "summaries" LEFTA
    [ "SUMMARY"; x = summary -> x ]
  ];
  
  summary:
  [ "summary" LEFTA
    [ x = LIST0 fml -> List.fold_left gen_conj (formula_of_heap HEmp loc) x ]
  ];

  fml:
  [ "fml" LEFTA
    [ "{"; x = pred; "}"; ";" -> x
    | x = ptr; "["; "label"; "="; y=ptr; "]"; ";" -> formula_of_pure_formula (mkEqVar x y loc) loc
    | x = ptr; "->"; y = ptr; "["; lbl; "]"; ";" -> formula_of_pure_formula (mkEqVar x y loc) loc
    ]
  ];

  pred:
  [ "pred" LEFTA
    [ x=lbl; ";"; y=preddef; LIST1 preddef -> 
      let typ,size = parse_lbl x in
      let heap = mkViewNode y typ [] loc in
      let pure = match size with
        | 1 -> mkNeqVar y Cpure.SV.zero (* (SpecVar (Named "", "null", Unprimed)) *) loc
        | _ -> mkTrue loc
      in
      normalize_combine_heap (formula_of_pure_formula pure loc) heap
    ]
  ];

  preddef:
  [ "preddef" LEFTA
    [ x = ptr; "["; "label"; "="; ptr; "]"; ";" -> x
    | x = ptr; "->"; ptr; "["; lbl; "]"; ";" -> x
    ]
  ];

  ptr:
  [ "ptr" LEFTA
    [ x = id -> SpecVar (Named "GenNode", x, Unprimed) ]
  ];  

  lbl:
  [ "lbl" NONA
    [ "label"; "="; "hasValue" -> None
    | "label"; "="; "AuxValue" -> None
    | "label"; "="; "SLS"; size=INT; "+" -> Some(1,size)
    | "label"; "="; "["; "+"; INT; "]" -> None
    ]
  ];

  id:
  [ "id" NONA
    [ x=INT -> x
    | x=LIDENT -> x
    | x=UIDENT -> x
(*    | "CL"; "#"; INT; ":"; x=SELF; "#"; INT -> x*)
(*    | "#"; x=INT; "["; "size"; "="; INT; "B"; "]" -> x*)
    | "next"; x=INT -> x
    | "tl"; x=INT -> x
    | "data"; x=INT -> x
    ]
  ];

END
	
let parse_shape s = Gram.parse_string expression (Loc.mk "<string>") s











