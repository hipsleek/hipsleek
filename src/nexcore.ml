(* this is meant as more efficient baga module *)
module EPUREN =
  functor (Elt : SV_TYPE) ->
  struct
    module EM = Gen.EqMap(Elt)
    type elem = Elt.t
    type epart = (elem list) list
    type emap = (EM.emap * epart)
    (* baga, eq_map, ineq_list *)
    (* type epure = (elem list * (elem * elem) list * (elem * elem) list) *)
    type epure = (elem list * emap * (elem * elem) list)
    type epure_disj = epure list
    let emap_empty = (EM.mkEmpty, [])
    let emap_empty_sv = (EMapSV.mkEmpty, [])
    let mk_false = ([Elt.zero], emap_empty, [])
    let mk_false_disj = []
    let mk_true = [([], emap_empty_sv, [])]

    let is_false (e:epure) = (e == mk_false)
    let pr1 = pr_list Elt.string_of
    let string_of_pair = pr_list (pr_pair Elt.string_of Elt.string_of)
    let pr2 = string_of_pair
    let string_of_epart lst = pr_list (pr_list Elt.string_of) lst
    let string_of (x:epure) =
      pr_triple (add_str "BAGA" pr1) (fun (_,ep) ->
          (add_str "EQ" string_of_epart) ep) (add_str "INEQ" pr2) x

    let string_of_all (x:epure) =
      pr_triple (add_str "BAGA" pr1) (fun ep ->
          (add_str "EQ" (pr_pair EM.string_of_debug string_of_epart)) ep) (add_str "INEQ" pr2) x

    let string_of_disj (x:epure_disj) = pr_list_ln string_of x
    let mk_data sv = [([sv], emap_empty, [])] 

    (* let mk_partition_x e= *)
    (*   let n_e = EM.partition e in *)
    (*   List.map EM.emap_sort n_e *)

    let mk_partition e = Debug.no_1 "partition" EM.string_of_debug string_of_epart EM.partition e

    let compare_list cmp b1 b2 =
      let rec aux b1 b2 =
        match b1,b2 with
        | [],[] -> 0
        | [],_ -> -1
        | _,[] ->1
        | (x::xs),(y::ys) ->
          let c = cmp x y in
          if c==0 then aux xs ys
          else c
      in aux b1 b2

    let partition_compare lst1 lst2 =
      compare_list (fun l1 l2 -> compare_list Elt.compare l1 l2) lst1 lst2

    let check_eqmap s  (eq,p)  =
      if !Globals.double_check then
        let p2 = mk_partition eq in
        if (partition_compare p p2) != 0 then
          begin
            x_binfo_pp ("Inconsistent eqmap @ "^s) no_pos;
            x_binfo_hp (add_str "eqmap" EM.string_of_debug) eq no_pos;
            x_binfo_hp (add_str "part" string_of_epart) p no_pos;
            x_binfo_hp (add_str "part2" string_of_epart) p2 no_pos;
          end

    let check_epure s ((_,eqmap,_) as r) =
      check_eqmap s eqmap 

    let check_epure_disj s lst =
      List.iter (check_epure s) lst 

    let baga_conv baga : formula =
      let baga = Elt.conv_var baga in
      if (List.length baga = 0) then
        mkTrue no_pos
      else if (List.length baga = 1) then
        mkGtVarInt (List.hd baga) 0 no_pos
      else
        let rec helper i j baga len =
          let f1 = mkNeqVar (List.nth baga i) (List.nth baga j) no_pos in
          if i = len - 2 && j = len - 1 then
            f1
          else if j = len - 1 then
            let f2 = helper (i + 1) (i + 2) baga len in
            mkAnd f1 f2 no_pos
          else
            let f2 = helper i (j + 1) baga len in
            mkAnd f1 f2 no_pos
        in
        let f1 = helper 0 1 baga (List.length baga) in
        let f2 = List.fold_left (fun f sv -> mkAnd f1 (mkGtVarInt sv 0 no_pos) no_pos)
            (mkGtVarInt (List.hd baga) 0 no_pos) (List.tl baga) in
        mkAnd f1 f2 no_pos


    let baga_enum baga : formula =
      let baga = Elt.conv_var baga in
      match baga with
      | [] -> mkTrue no_pos
      | h::ts ->
        let i = ref 1 in
        List.fold_left (fun f sv ->
            i := !i + 1;
            mkAnd f (mkEqVarInt sv !i no_pos) no_pos
          ) (mkEqVarInt (List.hd baga) !i no_pos) (List.tl baga)

    let merge_baga b1 b2 = Elt.merge_baga b1 b2
    let hull_baga b1 b2 = Elt.hull_baga b1 b2

    let merge cmp b1 b2 =
      let rec aux b1 b2 =
        match b1,b2 with
        | [],b | b,[] -> b
        | x1::t1, x2::t2 ->
          let c = cmp x1 x2 in
          if c<0 then x1::(aux t1 b2)
          else if c>0 then x2::(aux b1 t2)
          else x1::(aux t1 t2) in
      aux b1 b2

    (* pre : v1 < v2 *)
    (* baga ==> v1!=v2 *)
    let baga_imp baga v1 v2 =
      let rec find lst v =
        match lst with
        | [] -> None
        | x::xs -> if Elt.eq v x then Some xs
          else find xs v in
      match find baga v1 with
      | None -> false
      | Some rst -> not((find rst v2) == None)

    let pair_cmp (x1,x2) (y1,y2) =
      let c = Elt.compare x1 y1 in
      if c==0 then Elt.compare x2 y2
      else c

    let merge_ineq baga eq i1 i2 =
      let norm ((x,y) as p) =
        if baga_imp baga x y then []
        else if EM.is_equiv eq x y then failwith "contra with eqset"
        else [p] in
      let rec aux i1 i2 = match i1,i2 with
        | [],ineq | ineq,[] -> ineq
        | x::xs,y::ys ->
          let c = pair_cmp x y in
          if c==0 then (norm x) @ (aux xs ys)
          else if c<0 then (norm x) @ (aux xs i2)
          else (norm y) @ (aux i1 ys)
      in aux i1 i2

    (* return true if (x,y) in baga & (x,y) in eq *)
    let detect_contra eq baga =
      let rec aux b =
        match b with 
        | [] -> false
        | x::xs -> (EM.is_equiv eq Elt.zero x) || (aux2 x xs) || aux xs 
      and aux2 x xs = match xs with
        | [] -> false
        | y::ys -> 
          if EM.is_equiv eq x y then true
          else aux2 x ys
      in aux baga

    (* DONE : norm ineq1@ineq2 *)
    (* false not always detected yet *)
    let mk_star efp1 efp2 =
      if (is_false efp1) || (is_false efp2) then mk_false
      else
        (* let (baga1, (eq1,_), neq1) = efp1 in *)
        (* let (baga2, (eq2,_), neq2) = efp2 in *)
        match efp1,efp2 with
        | (baga1, (eq1,p1), neq1),(baga2, (eq2,p2), neq2) ->
          try
            if (detect_contra eq1 (baga2)) || (detect_contra eq2 (baga1)) 
            then mk_false
            else 
              let new_baga = merge_baga baga1 baga2 in
              (* x_tinfo_hp (add_str "eq1" EM.string_of_debug) eq1 no_pos; *)
              (* x_tinfo_hp (add_str "eq2" EM.string_of) eq2 no_pos; *)
              (* x_tinfo_hp (add_str "part2" string_of_epart) p2 no_pos; *)
              let new_eq = EM.merge_eset eq1 eq2 in
              let new_eq2 = (new_eq,mk_partition new_eq) in
              check_eqmap "mk_part:2" new_eq2;
              let new_neq = merge_ineq new_baga new_eq neq1 neq2 in
              (new_baga, new_eq2, new_neq)
          with _ -> mk_false


    let mk_star e1 e2 =
      check_epure "mk_star:1" e1;
      check_epure "mk_star:2" e2;
      let pr = string_of in
      Debug.no_2 "ex_mk_star" pr pr pr mk_star e1 e2


    (* [(a,[b,c])] --> a=b & a=c *)
    (* [(a,[b,c]),(d,[e])] --> a=b & a=c & d=e *)
    let conv_eq ((eq,_) : emap) : formula =
      let pairs = Elt.conv_var_pairs (EM.get_equiv eq)  in
      let fl = List.map (fun (v1,v2) ->
          if Globals.is_null (name_of_spec_var v1) then mkEqNull v2 v1 no_pos
          else mkEqVar v1 v2 no_pos
        ) pairs in
      List.fold_left (fun f1 f2 ->
          mkAnd f1 f2 no_pos
        ) (mkTrue no_pos) fl

    (* [(a,b);(b,c)] --> a!=b & b!=c *)
    let conv_ineq (ieq : (elem * elem) list) : formula  =
      let pairs = Elt.conv_var_pairs ieq  in
      List.fold_left (fun f1 (v1, v2) ->
          let f2 = mkNeqVar v1 v2 no_pos in
          mkAnd f1 f2 no_pos
        ) (mkTrue no_pos) pairs

    let conv_enum ((baga,eq,inq) : epure) : formula =
      let f1 = conv_eq eq in
      let f2 = conv_ineq inq in
      let bf = baga_enum baga in
      mkAnd bf (mkAnd f1 f2 no_pos) no_pos

    let conv ((baga,eq,inq) : epure) : formula =
      let f1 = conv_eq eq in
      let f2 = conv_ineq inq in
      let bf = baga_conv baga in
      mkAnd bf (mkAnd f1 f2 no_pos) no_pos

    let conv ((baga,eq,inq) as x : epure) : formula =
      let pr = string_of_all in
      Debug.no_1 "conv_one" pr !Cpure.print_formula conv x

    let is_zero b = match b with
      | [] -> false
      | x::_ -> Elt.is_zero x

    (* assume normalized *)
    let unsat ((baga,(eq,_),ieq) : epure) : bool =
      let zf = is_zero baga in
      (* zf *)
      if zf then true
      else List.exists (fun (v1,v2) -> EM.is_equiv eq v1 v2) ieq (* need it to remove (null,null) in ineq *)

    let unsat e =
      Debug.no_1 "ex_unsat" string_of string_of_bool unsat e
(*
    given (baga,eq,inq)
    contra if
       null \in baga
       duplicate (in baga - detected by merge)
       exists (a,b) in inq & eq
       exists (a,a) in inq (detected by norm,subs )

  how to detect:
       ([b], b=null, ..)?
  null is captured as _ which is the smallest
  value that is always used in baga.

*)

    let norm (efp) =
      if unsat efp then mk_false
      else efp

    let elim_unsat_disj disj =
      List.filter (fun f -> not(unsat f)) disj

    let is_false_disj disj =
      List.for_all (fun epf -> unsat epf) disj
      (* disj==[] *)

    let mk_false_disj = []

    (* this should follow ef_elim_exists_1 closely *)
    let elim_exists (svl : elem list) (f : epure) : epure =
      (* let subs_pair sst (e1,e2) = *)
      (*   let new_e1 = try *)
      (*     let (_, new_e1) = List.find (fun (v1,_) -> *)
      (*         Elt.eq e1 v1 *)
      (*     ) sst in *)
      (*     new_e1 *)
      (*   with Not_found -> e1 in *)
      (*   let new_e2 = try *)
      (*     let (_, new_e2) = List.find (fun (v1,_) -> *)
      (*         Elt.eq e2 v1 *)
      (*     ) sst in *)
      (*     new_e2 *)
      (*   with Not_found -> e2 in *)
      (*   if Elt.compare new_e1 new_e2 < 0 then *)
      (*     (new_e1, new_e2) *)
      (*   else *)
      (*     (new_e2, new_e1) *)
      (* in *)
      (* let filter_pairs svl eq ieq = *)
      (*   let new_eq = EM.build_eset (List.filter (fun (e1, e2) -> *)
      (*       not ((Elt.eq e1 e2) || *)
      (*           (List.exists (Elt.eq e1) svl) || *)
      (*           (List.exists (Elt.eq e2) svl)) *)
      (*   ) eq) in *)
      (*   let new_ieq = List.filter (fun (e1, e2) -> *)
      (*       if Elt.eq e1 e2 then failwith "exception -> mkFalse" *)
      (*       else *)
      (*         not ((List.exists (Elt.eq e1) svl) || *)
      (*             (List.exists (Elt.eq e2) svl)) *)
      (*   ) ieq in *)
      (*   (new_eq, new_ieq) *)
      (* in *)
      try
        let (baga, (eq,_), neq) = f in
        let p_aset = eq in
        let mk_subs =
          List.map
            (fun v ->
               let lst = EM.find_equiv_all v p_aset in
               let lst = List.sort Elt.compare lst in
               let free = List.filter (fun v -> not(List.exists (Elt.eq v) svl)) lst in
               match free with
               | [] -> (v,v)
               | f::_ -> (v,f)
            ) svl in
        let mk_subs = Elt.conv_var_pairs mk_subs in
        let svl_lst = Elt.conv_var svl in
        let locate v =
          (* throws exception if existential present *)
          if List.exists (fun e -> eq_spec_var e v) svl_lst then
            let (a,b) = List.find (fun (vv,_) -> eq_spec_var v vv) mk_subs in
            if a = b then
              failwith "exist var"
            else
              b
          else v (* free *) in
        let new_baga0 = Elt.from_var (List.fold_left (fun acc v ->
            try
              let b = locate v in
              b::acc
            with _ -> acc) [] (Elt.conv_var baga)) in
        (* duplicates possible? *)
        let duplicate baga =
          let rec aux p baga =
            match baga with
            | [] -> false
            | b::bl -> (Elt.eq p b) || (aux b bl)
          in match baga with
          | [] -> false
          | b::bl -> aux b bl
        in
        let new_baga = List.sort Elt.compare new_baga0 in
        let () = if duplicate new_baga then failwith "duplicate baga" else () in
        let new_eq = EM.elim_elems eq svl in
        let new_eq = (new_eq,mk_partition new_eq) in
        check_eqmap "mk_part:1" new_eq;
        (* let eq_pairs = EM.get_equiv eq in *)
        (* let subs_eq = List.map (subs_pair mk_subs) eq_pairs in *)
        let new_neq = Elt.from_var_pairs (List.fold_left (fun acc (v1,v2) ->
            let ans =
              try
                let b1 = locate v1 in
                let b2 = locate v2 in
                Some (b1,b2)
              with _ -> None in
            match ans with
            | None -> acc
            | Some (b1,b2) ->
              (* re-order? *)
              let c = compare_spec_var b1 b2 in
              if c < 0 then (b1,b2)::acc
              else if c==0 then failwith "INEQ contra detected"
              else (b2,b1)::acc
          ) [] (Elt.conv_var_pairs neq)) in
        let new_neq = List.sort pair_cmp new_neq in
        let rec remove_duplicate ineq =
          match ineq with
          | [] -> []
          | [hd] -> [hd]
          | hd1::hd2::tl ->
            if pair_cmp hd1 hd2 = 0 then
              remove_duplicate (hd2::tl)
            else
              hd1::(remove_duplicate(hd2::tl))
        in
        let new_neq = remove_duplicate new_neq in
        (* let subs_neq = List.map (subs_pair mk_subs) neq in *)
        (* let (new_eq, new_neq0) = filter_pairs svl subs_eq subs_neq in *)
        (* let new_neq = List.filter (fun (e1, e2) -> *)
        (*     not (List.exists (Elt.eq e1) new_baga && List.exists (Elt.eq e2) new_baga)) new_neq0 in *)
        (new_baga, new_eq, new_neq)
      with _ -> mk_false

    let elim_exists (svl : elem list) (f : epure) : epure =
      let pr1 = pr_list Elt.string_of in
      let r = Debug.no_2 "ef_elim_exists" pr1 (string_of) (string_of)
          (fun _ _ -> elim_exists svl f) svl f in
      let () = check_epure "elim_exists : result" r in
      r


    (* let imply (ante : epure) (conseq : epure) : bool = *)
    (*   let a_f = conv_enum ante in *)
    (*   let c_f = conv conseq in *)
    (*   (\* a_f --> c_f *\) *)
    (*   let f = mkAnd a_f (mkNot_s c_f) no_pos in *)
    (*   not (!is_sat_raw (Mcpure.mix_of_pure f)) *)

    let ef_conv_disj_ho conv disj : formula =
      List.fold_left (fun f ep ->
          mkOr f (conv ep) None no_pos
        ) (mkFalse no_pos) disj

    (* needed in cvutil.ml *)
    let ef_conv_enum_disj = ef_conv_disj_ho conv_enum

    let ef_conv_disj = ef_conv_disj_ho conv

    (* let eq_epure (ante : epure) (conseq : epure) : bool = *)
    (*   imply ante conseq && imply conseq ante *)


    let eq_list f b1 b2 =
      let rec aux b1 b2 =
        match b1,b2 with
        | [],[] -> true
        | [],_ -> false
        | _,[] -> false
        | (x::xs),(y::ys) ->
          if f x y then aux xs ys
          else false
      in aux b1 b2

    let rec baga_eq b1 b2 = eq_list Elt.eq b1 b2

    let rec baga_cmp b1 b2 = compare_list Elt.compare b1 b2
    (* match b1,b2 with *)
    (*   | [],[] -> true *)
    (*   | [],_ -> false *)
    (*   | _,[] -> false *)
    (*   | (x::xs),(y::ys) ->  *)
    (*         if Elt.eq x y then baga_eq xs ys *)
    (*         else false *)

    (* let compare_partition cmp p1 p2 = *)
    (*   let rec aux p1 p2 = *)
    (*     match p1,p2 with *)
    (*       | [],[] -> 0 *)
    (*       | [],_ -> -1 *)
    (*       | _,[] -> 1 *)
    (*       | x1::p1,x2::p2 -> *)
    (*             let c1=compare_list cmp x1 x2 in *)
    (*             if c1==0 then aux p1 p2 *)
    (*             else c1 *)
    (*   in aux p1 p2 *)

    let emap_compare (_,lst1) (_,lst2) =
      (* DONE : is get_equiv in sorted order? *)
      (* let lst1 = mk_partition e1 in *)
      (* let lst2 = mk_partition e2 in *)
      (* let lst1 = List.sort pair_cmp lst1 in *)
      (* let lst2 = List.sort pair_cmp lst2 in *)
      compare_list (fun l1 l2 -> compare_list Elt.compare l1 l2) lst1 lst2

    let emap_eq em1 em2 = (emap_compare em1 em2) == 0
    (* let ps1 = EM.get_equiv em1 in *)
    (* let ps2 = EM.get_equiv em2 in *)
    (* let imp em ps = *)
    (*   List.for_all (fun (v1,v2) -> EM.is_equiv em v1 v2) ps in *)
    (*   imp em1 ps2 && imp em2 ps1 *)

    (* assumes ine2 is non-redundant *)
    (* let ineq_imp (\* b1 *\) ine1 ine2 = *)
    (*   List.for_all (fun (v1,v2) -> *)
    (*   (\* (baga_imp b1 v1 v2) || *\)  *)
    (*       List.exists (fun (a1,a2) -> (Elt.eq a1 v1) && (Elt.eq a2 v2) ) ine1) ine2 *)

    (* let ineq_eq (\* b1 b2 *\) ine1 ine2 = *)
    (*   ineq_imp (\* b1 *\) ine1 ine2 && ineq_imp (\* b2 *\) ine2 ine1 *)

    let eq_diff (x1,x2) (y1,y2) = Elt.eq x1 y1 && Elt.eq x2 y2

    let ineq_compare (* b1 b2 *) ine1 ine2 = compare_list pair_cmp ine1 ine2

    (* more efficient in_eq assuming diff list is sorted *)
    let ineq_eq (* b1 b2 *) ine1 ine2 = (ineq_compare ine1 ine2) == 0
    (* eq_list eq_diff ine1 ine2 *)
    (* match ine1,ine2 with *)
    (*   | [], [] -> true *)
    (*   | [], _ -> false *)
    (*   | _,[] -> false *)
    (*   | x::xs,y::ys ->  *)
    (*         if eq_diff x y then ineq_eq xs ys *)
    (*         else false *)

    let eq_epure_syn ((b1,e1,in1) as ep1 : epure) ((b2,e2,in2) as ep2 : epure) : bool =
      (* assume non-false *)
      (baga_eq b1 b2) && (emap_eq e1 e2) && (ineq_eq in1 in2)

    (* get norm_eq from eqmap *)
    (* get domain; choose smallest *)
    (* filter as they are taken out *)
    (* let emap_extract e1 e2 = [] *)

    let epure_compare ((b1,e1,in1) as ep1 : epure) ((b2,e2,in2) as ep2 : epure) : int =
      (* assume non-false *)
      let c1 = baga_cmp b1 b2 in
      if c1==0 then
        let c2 = emap_compare e1 e2  in
        if c2==0 then
          ineq_compare in1 in2
        else c2
      else c1


    let norm_disj lst =
      let r = List.sort epure_compare lst in
      let rec aux p xs =
        match xs with
        | [] -> [p]
        | x::xs -> 
          if epure_compare p x ==0 then aux p xs
          else p::(aux x xs) in
      match r with
      | [] -> []
      | x::xs -> aux x xs

    (* TODO-WN why did we not sort this *)
    let mk_or_disj t1 t2 = 
      norm_disj (t1@t2)
    (* let res=t1@t2 in *)
    (*   List.sort epure_compare res *)

    let mk_or_norm t1 t2 = 
      mk_or_disj t1 t2
    (* let res=t1@t2 in *)
    (*     List.sort epure_compare res *)

    let elim_exists_disj (svl : elem list) (lst : epure_disj) : epure_disj =
      let r = List.map (fun e -> elim_exists svl e) lst in
      norm_disj r
    (* List.sort epure_compare r  *)

    let merge_disj lst1 lst2 =
      merge epure_compare lst1 lst2

    let merge_disj lst1 lst2 =
      let pr = string_of_disj in
      Debug.no_2 "ex_merge_disj" pr pr pr merge_disj lst1 lst2

    let add_star ep lst =
      let xs = List.map (fun v -> mk_star ep v) lst in
      let zs = List.filter (fun x -> not(unsat x)) xs in
      norm_disj zs
    (* List.sort epure_compare zs *)

    (* xs --> ys? *)
    let lst_imply cmp xs ys =
      let rec aux xs ys =
        match xs,ys with
        | _,[] -> true
        | [],_ -> false
        | x::xs2,y::ys2 ->
          let c = cmp x y in
          if c==0 then aux xs2 ys2
          else if c<0 then aux xs2 ys
          else false
      in aux xs ys

    let lst_imply_pair cmp xs ys =
      let pr = pr_list (pr_pair Elt.string_of Elt.string_of) in
      Debug.no_2 "ex_lst_imply_pair" pr pr string_of_bool (lst_imply cmp) xs ys


    (* let pair_compare cmp (a1,a2) (b1,b2) = *)
    (*   let c = cmp a1 b1 in *)
    (*   if c==0 then cmp a2 b2 *)
    (*   else c *)

    let emap_imply e1 e2 =
      (* let lst1 = EM.get_equiv e1 in *)
      let lst2 = EM.get_equiv e2 in
      List.for_all (fun (x,y) -> EM.is_equiv e1 x y) lst2

    let exists_baga b y =
      let rec aux b =
        match b with 
        | [] -> false
        | x::xs -> let c1 = Elt.compare x y  in
          if c1>0 then false
          else if c1==0 then true
          else aux xs
      in aux b

    let exists_baga_pair b y z =
      let rec aux b =
        match b with 
        | [] -> false
        | x::xs -> let c1 = Elt.compare x y (* x y  *)in
          if c1>0 then false
          else if c1==0 then exists_baga b z
          else aux xs
      in aux b

    (* epure syntactic imply *)
    (* we need b1 --> i2 or i1 -> i2, but the latter is now missing*)
    let epure_syn_imply (b1,(e1,p1),i1) (b2,(e2,p2),i2) =
      let f1 = lst_imply Elt.compare b1 b2 in
      if f1 then
        let null_el = Elt.zero (* mk_elem (mk_spec_var "null") *) in
        (* let f2 = List.for_all *)
        (*   (fun (x,y) -> (Elt.is_zero x && exists_baga b1 y) *)
        (*       || (exists_baga_pair b1 x y)) i2 in *)
        let i2_new = List.filter
            (fun (x,y) -> not((Elt.is_zero x && exists_baga b1 y) ||
                              (exists_baga_pair b1 x y))) i2 in
        (* (fun (x,y) -> (Elt.is_zero x && exists_baga b1 y) *)
        (*     || (exists_baga_pair b1 x y)) i2 in *)
        (* let i1_new = i1_new@i1 in *)
        (* let i1_new = List.fold_left (fun i1 el -> *)
        (*     let c = Elt.compare el null_el in *)
        (*     if c < 0 then *)
        (*       [(el, null_el)]@i1 *)
        (*     else if c > 0 then *)
        (*       [(null_el, el)]@i1 *)
        (*     else *)
        (*       failwith "fail in epure_syn_imply" *)
        (* ) i1 b1 in *)
        (* let i1_new = List.sort pair_cmp i1_new in *)
        let f2 = lst_imply_pair pair_cmp i1 i2_new in
        if f2 then emap_imply e1 e2 (* DONE: e1 --> e2? *)
        else false
      else false

    let syn_imply ep lst =
      List.exists (fun ep2 -> epure_syn_imply ep ep2) lst

    let syn_imply ep lst =
      let pr1 = string_of in
      let pr2 = string_of_disj in
      Debug.no_2 "ex_syn_imply" pr1 pr2 string_of_bool syn_imply ep lst

    let epure_disj_syn_imply lst1 lst2 =
      List.for_all (fun ep -> syn_imply ep lst2) lst1

    let epure_disj_syn_imply lst1 lst2 =
      let pr1 = string_of_disj in
      Debug.no_2 "ex_epure_disj_syn_imply" pr1 pr1 string_of_bool epure_disj_syn_imply lst1 lst2


    let sem_imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
      let a_f = ef_conv_enum_disj ante in
      let c_f = ef_conv_disj conseq in
      (* a_f --> c_f *)
      let f = mkAnd a_f (mkNot_s c_f) no_pos in
      not (x_add_1 !is_sat_raw (Mcpure.mix_of_pure f))

    let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
      let r = epure_disj_syn_imply ante conseq in
      if !Globals.double_check then
        begin
          let r2 = sem_imply_disj ante conseq in
          if r!=r2 then
            begin
              let pr = string_of_disj in
              x_tinfo_hp (add_str "ante" pr) ante no_pos;
              x_tinfo_hp (add_str "conseq" pr) conseq no_pos;
              x_tinfo_pp ("Got "^(string_of_bool r)^" but expects "^(string_of_bool r2)) no_pos
            end
        end;
      r

    let imply_disj (ante : epure_disj) (conseq : epure_disj) : bool =
      let pr1 = string_of_disj in
      Debug.no_2 "ex_imply_disj" pr1 pr1 string_of_bool imply_disj ante conseq

    (* let mk_star_disj (efpd1:epure_disj) (efpd2:epure_disj)  = *)
    (*   let res = *)
    (*     List.map (fun efp1 -> List.map (fun efp2 -> mk_star efp1 efp2) efpd2) efpd1 in *)
    (*   List.concat res *)

    let mk_star_disj_x (efpd1:epure_disj) (efpd2:epure_disj)  =
      let res =
        List.map (fun efp1 -> add_star efp1 efpd2) efpd1 in
      List.fold_left merge_disj [] res
    (* List.concat res *)

    let mk_star_disj (efpd1:epure_disj) (efpd2:epure_disj) =
      Debug.no_2 "I.mk_star_disj" string_of_disj string_of_disj string_of_disj
        mk_star_disj_x efpd1 efpd2


    (* reducing duplicate? *)
    (* let norm_disj disj = *)
    (*   let rec remove_duplicate (disj : epure_disj) : epure_disj = *)
    (*     match disj with *)
    (*       | [] -> [] *)
    (*       | hd::tl -> *)
    (*             let new_tl = remove_duplicate (List.filter (fun ep -> *)
    (*                 not (eq_epure_syn hd ep)) tl) in *)
    (*             hd::new_tl *)
    (*   in *)
    (*   let disj0 = List.filter (fun v -> not(is_false v)) (List.map norm disj) in *)
    (*   remove_duplicate disj0 *)

(*
            List.map (fun (baga, eq, ineq) ->
              let new_baga = subst_var_list sst baga in
              let eqf = EPureI.conv_eq eq in
              let new_eqf = subst sst eqf in
              let p_aset = pure_ptr_equations new_eqf in
              let new_eq = EMapSV.build_eset p_aset in
              let ineqf = EPureI.conv_ineq ineq in
              let new_ineqf = subst sst ineqf in
              let new_ineq = get_ineq new_ineqf in
              (* let new_pf = subst (List.combine view_args svl) pf in *)
              (new_baga, new_eq, new_ineq)
          ) efpd in
*)

    let subst_elem sst v =
      if Elt.is_zero v then v
      else try
          let (_,t) = List.find (fun (w,_) -> Elt.eq w v) sst in
          t
        with _ -> v (* should return v, not all elt have subst *) (* failwith ("subst_elem : cannot find elem "^Elt.string_of v) *)

    let subst_epure sst ((baga,(eq,p),ineq) as ep) = 
      let new_eq = (EM.subs_eset_par sst eq) in
      let subs_fn = subst_elem sst in
      let new_baga = List.map (subs_fn) baga in
      (* let new_p0= List.map (List.map subs_fn) p in *)
      (* let new_p = List.map (List.map subs_fn) p in *)
      (* sort equalities *)
      (* let new_p = List.map (List.sort Elt.compare) new_p0 in *)
      let new_ineq = List.map (fun (a,b) -> (subs_fn a,subs_fn b)) ineq in
      let eqm = (new_eq,mk_partition new_eq) in
      (new_baga,eqm,new_ineq)

    let subst_epure sst ep = 
      let pr1 = string_of_pair in
      let pr = string_of_all in
      let ans = Debug.no_2 "ex_subst_epure" pr1 pr pr subst_epure sst ep in
      let () = check_epure "subst_epure" ans in
      ans

    let subst_epure_disj sst (lst:epure_disj) =
      List.map (subst_epure sst) lst

    let subst_epure_disj sst (lst:epure_disj) =
      let pr1 = string_of_pair in
      let pr = string_of_disj in
      let ans = Debug.no_2 "ex_subst_epure_disj" pr1 pr pr subst_epure_disj sst (lst:epure_disj) in
      let () = check_epure_disj "subst_epure_disj" ans in
      ans

    let get_ineq (pf : formula) =
      let rec helper lconj = match lconj with
        | [] -> []
        | hd::tl -> ( match hd with
            | BForm ((Neq (e1, e2, _), _), _) ->
              ( match (e1,e2) with
                | (Var (sv1, _), Var (sv2, _)) ->
                  let c = compare_spec_var sv1 sv2 in
                  if c < 0 then
                    (sv1, sv2)::(helper tl)
                  else if c > 0 then
                    (sv2, sv1)::(helper tl)
                  else
                    failwith "fail in ineq"
                | (Var (sv, _), Null _)
                | (Null _, Var (sv, _)) ->
                  let null_var = List.hd (Elt.conv_var [Elt.zero]) (* mk_spec_var "null" *) in
                  let c = compare_spec_var null_var sv in
                  if c < 0 then
                    (null_var, sv)::(helper tl)
                  else if c > 0 then
                    (sv, null_var)::(helper tl)
                  else
                    failwith "fail in ineq"
                | (Null _, Null _) ->
                  failwith "fail in get_ineq"
                | _ -> helper tl
              )
            | _ -> helper tl
          )
      in
      List.sort pair_cmp (Elt.from_var_pairs (helper (split_conjunctions pf)))

    (* let get_baga (pf : formula) = *)
    (*   let rec helper lconj = match lconj with *)
    (*     | [] -> [] *)
    (*     | hd::tl -> ( match hd with *)
    (*         | BForm ((Neq (e1, e2, _), _), _) -> *)
    (*             ( match (e1,e2) with *)
    (*               | (Var (sv, _), Null _) *)
    (*               | (Null _, Var (sv, _)) -> *)
    (*                     sv::(helper tl) *)
    (*               | (Null _, Null _) -> *)
    (*                     failwith "fail in get_baga" *)
    (*               | _ -> helper tl *)
    (*             ) *)
    (*         | _ -> helper tl *)
    (*       ) *)
    (*   in *)
    (*   List.sort Elt.compare (Elt.from_var (helper (split_conjunctions pf))) *)

    (* TODO-EXPURE : has this been normalized? *)
    let mk_epure (pf:formula) =
      let p_aset = pure_ptr_equations pf in
      let p_aset = EM.build_eset (Elt.from_var_pairs p_aset) in
      let baga = (* get_baga pf in *) [] in
      let ineq = get_ineq pf in
      (* [([], pf)] *)
      if List.exists (fun (x,y) -> EM.is_equiv p_aset x y) ineq then []
      else 
        let pa = (p_aset,mk_partition p_aset)in
        check_eqmap "mk_part:3" pa;
        [(baga, pa, ineq)] (* new expure, need to add ineq : DONE *)

    let mk_epure (pf:formula) =
      let r = Debug.no_1  "ex_mk_epure" !print_pure_formula string_of_disj mk_epure (pf:formula) in
      check_epure_disj "mk_epure : result" r;
      r

    (* let to_cpure ((baga,eq,ineq) : epure) = *)
    (*   let f1 = conv_eq eq in *)
    (*   let f2 = conv_ineq ineq in *)
    (*   (baga, mkAnd f1 f2 no_pos) *)

    (* let to_cpure_disj (epd : epure_disj) = *)
    (*   List.map (fun ep -> to_cpure ep) epd *)

    let get_baga (epd : epure_disj) =
      if List.length epd = 0 then []
      else
        List.fold_left (fun acc (baga,_,_) ->
            Gen.BList.intersect_eq Elt.eq acc baga
        ) ((fun (a,_,_) -> a) (List.hd epd)) (List.tl epd)

    let to_cpure (ep : epure) = ep

    let to_cpure_disj (epd : epure_disj) = epd

    (* let from_cpure ((baga,pf) : ef_pure) = *)
    (*   let p_aset = pure_ptr_equations pf in *)
    (*   let p_aset = EMapSV.build_eset p_aset in *)
    (*   let ineq = get_ineq pf in *)
    (*   (baga, p_aset, ineq) *)

    (* let from_cpure_disj (epd : ef_pure_disj) = *)
    (*   List.map (fun ep -> from_cpure ep) epd *)

    let from_cpure (ep : epure) = ep

    let from_cpure_disj (epd : epure_disj) = epd

    (* TODO

       1. complete conv_eq & conv_neq
       2. complete elim_exists
       3. eq_epure ep1 ep2 (detect if two epures are equal, after norm)
       4. sort_epure_disj  (baga,...)
       5. strong_norm_epure (* must detect false, no x=x *)

    *)

  end
