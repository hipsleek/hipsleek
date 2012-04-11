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

let pre = Gram.Entry.mk "pre";;

let post = Gram.Entry.mk "post";;

let fml = Gram.Entry.mk "fml";;

let pred = Gram.Entry.mk "pred";;

let preddef = Gram.Entry.mk "preddef";;

let ptr = Gram.Entry.mk "ptr";;

let lbl = Gram.Entry.mk "lbl";;

let id = Gram.Entry.mk "id";;

let gen_conj x y = normalize 1 x y loc;;

let parse_lbl x = match x with
  | None -> ""
  | Some (1,n) -> "ll";;

EXTEND Gram
GLOBAL: expression pre post fml pred preddef ptr lbl id;
  expression:
  [ "expression" LEFTA
    [ "SUMMARY"; x = pre; "SUMMARY"; y = post -> (x,y) ]
  ];

  pre:
  [ "pre" LEFTA
    [ x = LIST1 fml -> List.fold_left gen_conj (formula_of_heap HTrue loc) x ]
  ];

  post:
  [ "post" LEFTA
    [ x = LIST1 fml -> List.fold_left gen_conj (formula_of_heap HTrue loc) x ]
  ];

  fml:
  [ "fml" LEFTA
    [ "{"; x = pred; "}"; ";" -> formula_of_heap x loc
    | x = ptr; "["; "label"; "="; y=ptr; "]"; ";" -> formula_of_pure_formula (mkEqVar x y loc) loc
    | x = ptr; "->"; y = ptr; "["; lbl; "]"; ";" -> formula_of_pure_formula (mkEqVar x y loc) loc
    ]
  ];

  pred:
  [ "pred" LEFTA
    [ x=lbl; ";"; y=preddef; LIST1 preddef -> mkViewNode y (parse_lbl x) [] loc ]
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
    | "CL"; "#"; INT; ":"; x=SELF; "#"; INT -> x
    | "#"; x=INT; "["; "size"; "="; INT; "B"; "]" -> x
    | "next"; x=INT -> x
    ]
  ];

END
	
let parse_shape s = Gram.parse_string expression (Loc.mk "<string>") s











