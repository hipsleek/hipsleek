open Globals
open GlobProver
open Gen.Basic
open Cpure

let gen_pai_form = ref true
let pai_file = open_log_out("pai.ml")

(*Convert to PAI format for dumping into a file and testing with PAI decision procedure *)
let pai_of_spec_var (sv : spec_var):string = match sv with
  | SpecVar (t, v, p) -> 
		let r = match (List.filter (fun (a,b,_)-> ((String.compare v b)==0) )!omega_subst_lst) with
				  | []->
            let ln = (String.length v) in  
            let r_c = if (ln<15) then v
              else 
                let v_s = String.sub v (ln-15)  15 in
                if((String.get v_s 0)=='_') then String.sub v_s 1 ((String.length v_s)-1) else v_s in
            begin
              omega_subst_lst := (r_c,v,t)::!omega_subst_lst; 
							r_c end
					| (a,b,_)::h->  a in 
		r ^ (if is_primed sv then Oclexer.primed_str else "")


let rec pai_of_exp e0 = match e0 with
  | Null _ -> "0"
  | Var (sv, _) -> pai_of_spec_var sv
  | IConst (i, _) -> string_of_int i 
  | AConst (i, _) -> string_of_int(int_of_heap_ann i) 
  | Add (a1, a2, _) ->  (pai_of_exp a1)^ " + " ^(pai_of_exp a2) 
  | Subtract (a1, a2, _) ->  (pai_of_exp a1)^ " - " ^"("^(pai_of_exp a2)^")"
  | Mult (a1, a2, l) ->
      let r = match a1 with
        | IConst (i, _) -> (string_of_int i) ^ "(" ^ (pai_of_exp a2) ^ ")"
        | _ -> let rr = match a2 with
            | IConst (i, _) -> (string_of_int i) ^ "(" ^ (pai_of_exp a1) ^ ")"
            | _ -> illegal_format "[pai.ml] Non-linear arithmetic is not supported by pai."
                (* Error.report_error { *)
                (*   Error.error_loc = l; *)
                (*   Error.error_text = "[pai.ml] Non-linear arithmetic is not supported by Pai." *)
                (* } *)
            in rr
      in r
  | Div (_, _, l) -> illegal_format "[pai.ml] Divide is not supported by pai."
      (* Error.report_error { *)
      (*   Error.error_loc = l; *)
      (*   Error.error_text ="[pai.ml] Divide is not supported." *)
      (* } *)
  | Max _
  | Min _ -> illegal_format ("pai.pai_of_exp: min/max should not appear here")
  | TypeCast _ -> illegal_format ("pai.pai_of_exp: TypeCast should not appear here")
  | FConst _ -> illegal_format ("pai.pai_of_exp: FConst")
  | Func _ -> "0" (* TODO: Need to handle *)
  | _ -> illegal_format ("pai.pai_of_exp: array, bag or list constraint "^(!print_exp e0))
(*
(ArrayAt _|ListReverse _|ListAppend _|ListLength _|ListTail _|ListHead _|
ListCons _|List _|BagDiff _|BagIntersect _|BagUnion _|Bag _|FConst _)
*)

(* and pai_ptr_eq_null a1 = *)
(*   let v= pai_of_exp a1 in *)
(*   if !Globals.ptr_to_int_exact then ("("^v^" = 0)") *)
(*   else ("("^v^" < 1)") *)

(* and pai_ptr_neq_null a1 = *)
(*   let v= pai_of_exp a1 in *)
(*   if !Globals.ptr_to_int_exact then (v^" != 0") *)
(*   else (v^" > 0") *)

and pai_of_b_formula b =
  let (pf, _) = b in
  match pf with
  | BConst (c, _) -> if c then "(0=0)" else "(0>0)"
  | XPure _ -> "(0=0)"
  | BVar (bv, _) ->  (pai_of_spec_var bv) ^ " > 0" (* easy to track boolean var *)
  | Lt (a1, a2, _) ->(pai_of_exp a1) ^ " < " ^ (pai_of_exp a2)
  | Lte (a1, a2, _) -> (pai_of_exp a1) ^ " <= " ^ (pai_of_exp a2)
  | Gt (a1, a2, _) ->  (pai_of_exp a1) ^ " > " ^ (pai_of_exp a2)
  | Gte (a1, a2, _) -> (pai_of_exp a1) ^ " >= " ^ (pai_of_exp a2)
  | SubAnn (a1, a2, _) -> (pai_of_exp a1) ^ " <= " ^ (pai_of_exp a2)
  (* | LexVar (_, a1, a2, _) -> "(0=0)" *)
  | Eq (a1, a2, _) -> begin
        (* if is_null a2 then *)
        (*   pai_ptr_eq_null a1 *)
        (*   (\* let v= pai_of_exp a1 in *\) *)
        (*   (\* if !Globals.ptr_to_int_exact then *\) *)
        (*   (\*   ("("^v^" < 1)") *\) *)
        (*   (\* else ("("^v^" = 0)") *\) *)
        (*   (\* ("("^v^" < 1 && "^v^" = xxxnull)") *\) *)
        (* else if is_null a1 then  *)
        (*   pai_ptr_eq_null a2 *)
        (*   (\* let v= pai_of_exp a2 in *\) *)
        (*   (\* ("("^v^" < 1)") *\) *)
        (*   (\* ("("^v^ " < 1 && "^v^" = xxxnull)") *\) *)
        (* else  *)
          (pai_of_exp a1) ^ " = " ^ (pai_of_exp a2)
  end
  | Neq (a1, a2, _) -> begin
        (* if is_null a2 then *)
        (*   pai_ptr_neq_null a1 *)
        (*       (\* (pai_of_exp a1) ^ " > 0" *\) *)
        (* else if is_null a1 then *)
        (*   pai_ptr_neq_null a2 *)
        (*   (\* (pai_of_exp a2) ^ " > 0" *\) *)
        (* else  *)
          " ~ " ^ (pai_of_exp a1)^ " = " ^ (pai_of_exp a2)
    end
  | EqMax (a1, a2, a3, _) ->
      let a1str = pai_of_exp a1 in
      let a2str = pai_of_exp a2 in
      let a3str = pai_of_exp a3 in
        "((" ^ a2str ^ " >= " ^ a3str ^ " /\\ " ^ a1str ^ " = " ^ a2str ^ ") \\/ ("
        ^ a3str ^ " > " ^ a2str ^ " /\\ " ^ a1str ^ " = " ^ a3str ^ "))"
  | EqMin (a1, a2, a3, _) ->
      let a1str = pai_of_exp a1  in
      let a2str = pai_of_exp a2  in
      let a3str = pai_of_exp a3  in
        "((" ^ a2str ^ " >= " ^ a3str ^ " /\\ " ^ a1str ^ " = " ^ a3str ^ ") \\/ ("
        ^ a3str ^ " > " ^ a2str ^ " /\\ " ^ a1str ^ " = " ^ a2str ^ "))"
  | VarPerm _ -> illegal_format ("pai.pai_of_exp: VarPerm constraint")
  | RelForm _ -> illegal_format ("pai.pai_of_exp: RelForm")
  | LexVar _ -> illegal_format ("pai.pai_of_exp: LexVar 3")
  | _ -> illegal_format ("pai.pai_of_exp: bag or list constraint")

and pai_of_formula pr_w pr_s f  =
  let rec helper f = 
    match f with
  | BForm ((b,_) as bf,_) -> 		
        begin
          match (pr_w b) with
            | None -> "(" ^ (pai_of_b_formula bf) ^ ")"
            | Some f -> helper f
        end
  | AndList _ ->
        begin
          let _ = print_endline ("AndList:?"^(!print_formula f)) in
          report_error no_pos "pai.ml: encountered AndList, should have been already handled"
        end
  | And (p1, p2, _) -> 	"(" ^ (helper p1) ^ " /\\ " ^ (helper p2 ) ^ ")"
  | Or (p1, p2,_ , _) -> "(" ^ (helper p1) ^ "\\/ " ^ (helper p2) ^ ")"
  | Not (p,_ , _) ->       " (~ (" ^ (pai_of_formula pr_s pr_w p) ^ ")) "	
  | Forall (sv, p,_ , _) -> " forall " ^ (pai_of_spec_var sv) ^ " . (" ^ (helper p) ^ ")"
  | Exists (sv, p,_ , _) -> " exists " ^ (pai_of_spec_var sv) ^ " . (" ^ (helper p) ^ ")"
  in 
  try
	helper f
  with _ as e -> 
      let s = Printexc.to_string e in
      let _ = print_string ("pai Error pai Exp:"^s^"\n Formula:"^(!print_formula f)^"\n") in
      (* let _ = Debug.trace_hprint (add_str "Pai Error format:" !print_formula) f in *)
      raise e
