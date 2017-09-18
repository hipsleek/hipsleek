#include "xdebug.cppo"
open Array_formula
(* open Array_formula_plus *)
open Format

type biabFormula =
  | BBaseNeg of (Cpure.formula list)
  | BBaseImply of (Cpure.formula list * Cpure.formula list * aseg_pred_plus list * aseg_pred_plus list)
  | BExists of (Cpure.spec_var list * biabFormula)
  | BForall of (Cpure.spec_var list * biabFormula)
  | BAnd of (biabFormula list)
  | BOr of (biabFormula list)
  | BNot of biabFormula
;;

let rec str_biabFormula f =  
  match f with
  | BBaseNeg plst ->
     "{NOT "^(str_list !str_pformula plst)^"}"
  | BBaseImply (lplst, rplst, frame, antiframe) ->
     "{"^(str_list !str_pformula lplst)^"==>"^(str_list !str_pformula rplst)^" @"^(str_aseg_pred_plus_lst frame)^" * "^(str_aseg_pred_plus_lst antiframe)^"}"
  | BExists (vset, nf) ->
     if List.length vset = 0
     then str_biabFormula nf
     else "Exists "^(str_list !str_sv vset)^": "^(str_biabFormula nf)
  | BForall (vset, nf) ->
     if List.length vset = 0
     then str_biabFormula nf
     else "Forall "^(str_list !str_sv vset)^": "^(str_biabFormula nf)
  | BAnd flst ->
     str_list_delimeter str_biabFormula flst "/\\" ""
  | BOr flst ->
     str_list_delimeter str_biabFormula flst "\\/" ""  
  | BNot nf ->
     "not("^(str_biabFormula nf)^")"
;;

(* let print_indent_list lst indent = *)
(*   List.fold_left *)
(*     (fun r item -> *)
(*       r^"\n"^(print_indent indent item)) *)
(*     "" lst *)
(* ;; *)
      

let rec str_pre_condition f =
  
  let rec helper f indent =
    match f with
    | BBaseNeg plst ->       
       print_indent indent ("{ NOT "^(str_list !str_pformula plst)^" }")      
    | BBaseImply (lplst, rplst, frame, antiframe) ->
       print_indent indent ("{ "^(str_list !str_pformula lplst)^"==>"^(str_list !str_pformula rplst)^" @"^(str_aseg_pred_plus_lst frame)^" * "^(str_aseg_pred_plus_lst antiframe)^" }")
    | BExists (vset, nf) ->
       (* if List.length vset = 0 *)
       (* then helper nf indent *)
       (* else *)
       (print_indent indent ("Exists "^(str_list !str_sv vset)^": "))^"\n"
       ^(helper nf (indent+1))
    | BForall (vset, nf) ->
       if List.length vset = 0
       then helper nf indent
       else
         (print_indent indent (("Forall "^(str_list !str_sv vset)^": ")^"\n"
                               ^(helper nf (indent+1))))
    | BAnd flst ->
       (print_indent indent ("AND"))
       ^(List.fold_left (fun r item -> r^"\n"^item) "" (List.map (fun item -> helper item (indent+1)) flst))
    | BOr flst ->
       (print_indent indent ("OR"))
       ^(List.fold_left (fun r item -> r^"\n"^item) "" (List.map (fun item -> helper item (indent+1)) flst))
       (* let s = (List.fold_left (fun r item -> item^" @, "^r) "" (List.map (fun f -> helper f 0) flst)) in *)
       (* let () = print_endline s in        *)
       (* sprintf ("@[<v>%s @, @[<v> "^^(Scanf.format_from_string s "" )^^" @]@]") "OR" *)
       (* (print_indent indent (("OR \n") *)
       (*                       ^(print_indent_list (List.map (fun f -> helper f (indent+1)) flst) 1))) *)

    | BNot nf ->
       failwith "str_pre_condition: TO BE IMPLEMENTED"
  in
  helper f 0
;;
  
let mkBBaseNeg plst =
  BBaseNeg plst
;;

let mkBBaseImply lplst rplst frame antiframe =
  BBaseImply (lplst, rplst, frame, antiframe) 
;;

let mkBAnd flst =
  BAnd (List.fold_left
          (fun r item ->
            match item with
            | BAnd flst1 ->
               flst1@r
            | _ -> item::r )
          [] flst)
;;

let mkBOr flst =
  BOr (List.fold_left
          (fun r item ->
            match item with
            | BOr flst1 ->
               flst1@r
            | _ -> item::r )
          [] flst)
;;
  
let mkBExists (vset,f) =
  if List.length vset = 0
  then f
  else BExists (vset,f)
;;

let mkBForall (vset,f) =
  if List.length vset = 0
  then f
  else BForall (vset,f)
;;

(* ONLY FOR CLASSICAL ENTAILMENT *)
let biabFormula_to_pure_classical f =
  let rec helper f =
    match f with
    | BBaseNeg plst ->
       (mkNot (mkAndlst plst))
    | BBaseImply (lplst, rplst, frame, antiframe) ->
       if List.length frame = 0 && List.length antiframe = 0
       then
         simplify (mkImply (mkAndlst lplst) (mkAndlst rplst))
       else
         simplify (mkImply (mkAndlst lplst) (mkFalse ()))
    | BExists (vset, nf) ->
       if List.length vset = 0
       then helper nf
       else (mkExists vset (helper nf))
    | BForall (vset, nf) ->
       if List.length vset = 0
       then helper nf
       else simplify (mkForall vset (helper nf))
    | BAnd flst ->
       simplify (mkAndlst (List.map helper flst))
    | BOr flst ->
       simplify (mkOrlst (List.map helper flst))
    | BNot nf ->
       simplify (mkNot (helper nf))
  in
  let newf = helper f in
  let () = y_binfo_pp (!str_pformula newf) in
  newf
;;

let check_validity f =
  let pf = biabFormula_to_pure_classical f in
  isValid pf
;;
        
