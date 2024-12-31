open Sleekapi
open Hipsleek_common

(* Put global initialization (e.g. declarations) before all others. *)
module Expect_test_config = struct
  include Expect_test_config
  let () =
    ForwardVerifier.init [];
    (* Initialize some definitions that our tests will use *)
    let register_declaration decl =
      match parse_decl decl with
      | Pred p -> predicate_decl p;
      | Lemma l -> lemma_decl l true;
      | _ -> raise (Invalid_argument "Declaration is not valid")
    in

    data_decl_cons "node" [(Int, "val"); (Named("node"), "next")];

    register_declaration  "pred ll<n> == self = null & n = 0 or self::node<next = r> * r::ll<n - 1> inv n >= 0.";
    register_declaration "pred sortl<n, mi> == self = null & n = 0 or self::node<mi, r> * r::sortl<n - 1, k> & mi <= k inv n >= 0.";
    register_declaration "lemma self::sortl<n, mi> -> self::ll<n>.";

end


(* These tests correspond to the entailment checking tests, but they also check for the frame. *)
open Formula
open Pure_formula
open Pure_expression
open Heap_formula
open Meta_formula

let check antes conseq =
  let result = EntailmentProver.entail_with_frame antes conseq in
  Printf.printf "%s\n" (EntailmentProver.string_of_result result)

let%expect_test "entailment smoke test" =
  check [(Meta_formula.of_heap_and_pure emp true_f)] (Structured.of_heap_and_pure emp true_f);
  [%expect{| |}]

let%expect_test "pure integer entailment" =
  let x = Identifier.make "x" in
  let x_prime = Identifier.primed "x" in
  check [(Meta_formula.of_heap_and_pure emp (and_f (gt (var x) (intl 0)) (eq (var x_prime) (intl 1))))]
    (Structured.of_heap_and_pure emp (gt (var x_prime) (intl 1)));
  [%expect{| |}]

let%expect_test "heap entailment reflexivity" =
  let x = Identifier.make "x" in
  check [(Meta_formula.of_heap_and_pure (points_to_int x 1) true_f)] (Structured.of_heap_and_pure (points_to_int x 1) true_f);
  [%expect{| |}]

let%expect_test "data view entailment" =
  let x = Identifier.make "x" in
  check [(Meta_formula.of_heap_and_pure (points_to x "node" [(intl 1); null]) true_f)]
    (Structured.of_heap_and_pure emp (not_f (eq (var x) null)));
  [%expect{| |}]

let%expect_test "pred view entailment" =
  let x = Identifier.make "x" in
  check [(Meta_formula.of_heap_and_pure emp (eq (var x) null))] (Structured.of_heap_and_pure (points_to x "ll" [(intl 0)]) true_f);
  [%expect{| |}]

let%expect_test "frame rule" =
  let y = Identifier.make "y" in
  let x = Identifier.make "x" in
  check [(Meta_formula.of_heap_and_pure (sep (points_to_int y 1) (points_to_int x 2)) true_f)] (Structured.of_heap_and_pure (points_to_int x 2) true_f);
  [%expect{| |}]

let%expect_test "lemma entailment" =
  let x = Identifier.make "x" in
  let a = Identifier.make "a" in
  let b = Identifier.make "b" in
  check [Meta_formula.of_heap_and_pure (points_to x "sortl" [var a; var b]) true_f] (Structured.of_heap_and_pure (points_to x "ll" [var a]) true_f);
  [%expect{| |}]

let%expect_test "linked list chaining" =
  let x = Identifier.make "x" in
  let r1 = Identifier.make "r1" in
  let c = Identifier.make "c" in
  let anon = Identifier.anon in
  check [Meta_formula.of_heap_and_pure (sep (points_to x "node" [var (anon ()); var r1]) (points_to x "node" [var (anon ()); null])) true_f]
    (Structured.of_heap_and_pure (points_to x "ll" [var c]) true_f);
  [%expect{| |}]

let%expect_test "Entailment checking" =
  let open EntailmentProver in
  let entail_1 () =
    (* true |- true *)
    let true_f = true_f in
    let empty_heap_f = empty_heap_f in
    let ante_f = ante_f empty_heap_f true_f in
    let conseq_f = conseq_f empty_heap_f true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_2 () =
    (* x |-> 1 |- x |-> 1 *)
    let ante_f = ante_f (points_to_int_f "x" 1)
        (true_f) in
    let conseq_f = conseq_f (points_to_int_f "x" 1)
        (true_f) in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_3 () =
    (* x > 0 /\ x' = x + 1 |- x' > 1 *)
    let ante_f = ante_f empty_heap_f
        (and_f
           (gt_pure_f
              (var_pure_exp "x")
              (int_pure_exp 0))
           (eq_pure_f
              (var_pure_exp "x'")
              (add_pure_exp
                 (var_pure_exp "x")
                 (int_pure_exp 1)))) in
    let conseq_f = conseq_f empty_heap_f
        (gt_pure_f
           (var_pure_exp "x'")
           (int_pure_exp 1)) in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_4 () =
    (* x::node<0,null> |- x != null *)
    (* let () = data_decl "data node { int val ; node next }." in *)
    let ante_f = ante_f 
        (points_to_f "x" "node" [(int_pure_exp 0); (null_pure_exp)]) true_f in
    let conseq_f = conseq_f empty_heap_f
        (not_f (eq_pure_f
                  (var_pure_exp "x")
                  null_pure_exp)) in
    let _ = entail ante_f conseq_f in
    ()
  in
    
  let entail_5 () =  
    (* x=null |- x::ll<0> *)
    let ante_f = ante_f empty_heap_f
        (eq_pure_f
           (var_pure_exp "x")
           null_pure_exp) in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(int_pure_exp 0)])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_6 () =
    (* x::ll<n> |- x::ll<n+1> *)
    let ante_f = ante_f
        (points_to_f "x" "ll" [(var_pure_exp "n")])
        true_f in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(add_pure_exp
                                  (var_pure_exp "n")
                                  (int_pure_exp 1)
                               )])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_7 () =
    (* x |-> 1 * y |-> 2 |- x -> 1 *)
    let h1 = points_to_int_f "x" 1 in
    let h2 = points_to_int_f "y" 2 in 
    let astar = sep_conj_f h1 h2 in
    let ante_f = ante_f astar true_f in
    let conseq_f = conseq_f (points_to_int_f "x" 1) true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_8 () =
    (* let _ = top_level_decl lemma in *)
    let ante_f = ante_f
        (points_to_f "x" "sortl" [(var_pure_exp "a");
                                  (var_pure_exp "b")])
        true_f in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(var_pure_exp "a")])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_9 () =
    (* x:: node(_, r1) * r1:: node(_, null) |-> x:: ll<c> *)
    let h1 = points_to_f "x" "node" [(var_pure_exp "_"); var_pure_exp "r1"] in
    let h2 = points_to_f "r1" "node" [(var_pure_exp "_"); (null_pure_exp)] in 
    let astar = sep_conj_f h1 h2 in
    let ante_f = ante_f astar true_f in
    let conseq_f = conseq_f (points_to_f "x" "ll" [(var_pure_exp "c")]) true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  entail_1 ();
  [%expect{| true |}];
  entail_2 ();
  [%expect{| true |}];
  entail_3 ();
  [%expect{| true |}];
  entail_4 ();
  [%expect{| true |}];
  entail_5 ();
  [%expect{| true |}];
  entail_6 ();
  [%expect{| false |}];
  entail_7 ();
  [%expect{| true |}];
  entail_8 ();
  [%expect{|
    Entailing lemma lem_2500: Valid.

    true |}];
  entail_9 ();
  [%expect{| true |}]

let%expect_test "Forward verification" =
  let open ForwardVerifier in


  let verify_1 () =
    (*
       int foo()
       requires true
       ensures res=1;
       {
       if (true)
       return 1;
       else
       return 2;
       }

       {(boolean v_bool_5_2020;
       (v_bool_5_2020 = true;
       if (v_bool_5_2020) [LABEL! 144,0: (int v_int_6_2018;
       (v_int_6_2018 = 1;
       ret# v_int_6_2018))]
       else [LABEL! 144,1: (int v_int_8_2019;
       (v_int_8_2019 = 2;
       ret# v_int_8_2019))]
       ))}
    *)
    let cstruc_form = spec_decl "foo" "requires true ensures res = 1;" [] Int false in
    let lfe = init_ctx cstruc_form in
    (* VarDecl : do nothing *)
    (* Assignment : check rhs exp  *)
    let lfe = upd_result_with_bool lfe true in
    (* Assignment : update res *)
    let lfe = add_assign_to_ctx lfe Bool "v_bool_5_2020" in

    (* Cond : then branch *)
    let then_lfe = add_cond_to_ctx lfe "v_bool_5_2020" true in
    let then_lfe = upd_result_with_int then_lfe 1 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_6_2018" in
    let then_lfe = upd_result_with_var then_lfe Int "v_int_6_2018" in
    (* Cond : else branch *)
    let else_lfe = add_cond_to_ctx lfe "v_bool_5_2020" false in
    let else_lfe = upd_result_with_int else_lfe 2 in
    let else_lfe = add_assign_to_ctx else_lfe Int "v_int_8_2019" in
    let else_lfe = upd_result_with_var else_lfe Int "v_int_8_2019" in

    let lfe = disj_of_ctx then_lfe else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)))
  in

  let verify_2 () =
    let add_param_list = [{param_type = Int; param_name = "a"; param_mod = RefMod;};
                          {param_type = Int; param_name = "b"; param_mod = RefMod;}] in
    let add_spec = spec_decl "add___" "requires true ensures res = a + b;"
        add_param_list Int false in
    (* let add_specs = spec_decl_x "int add(int a, int b)"
       "requires true ensures res = a + b;" in *)
    (*
       int incr(int i)
         requires true
         ensures res=i+1;
       {
         return i + 1;
       }

       {(int v_int_22_2043;
       (v_int_22_2043 = {((int v_int_22_2042;
       v_int_22_2042 = 1);
       add___$int~int(i,v_int_22_2042))};
       ret# v_int_22_2043))}
    *)
    let cstruc_form = spec_decl "incr" "requires true ensures res=i+1;"
        [{param_type = Int; param_name = "i"; param_mod = RefMod;}] Int false in
    let lfe = init_ctx cstruc_form in
    (* VarDecl : do nothing *)
    (* Assignment : check rhs exp *)
    (*   VarDecl : do nothing *)
    (*   Assignment : check rhs exp *)
    let lfe = upd_result_with_int lfe 1 in
    (*   Assignment : assign *)
    let lfe = add_assign_to_ctx lfe Int "v_int_22_2042" in
    (*   Call : check pre cond *)
    (* let lfe = check_pre_post lfe add_specs false add_param_list ["i"; "v_int_22_2042"] in *)
    let lfe = check_pre_post_str lfe "add___$int~int" ["i"; "v_int_22_2042"] in
    (* Assignment : assign *)
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Int "v_int_22_2043" in
    (* ret : update res *)
    let lfe = upd_result_with_var lfe Int "v_int_22_2043" in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form))) in

  let verify_3 () =
    let add_param_list = [{param_type = Int; param_name = "a"; param_mod = RefMod;};
                          {param_type = Int; param_name = "b"; param_mod = RefMod;}] in
    let add_specs = spec_decl "add__" "requires true ensures res = a + b;"
        add_param_list Int false in

    let is_null_param_list =
      [{param_type = Named "node"; param_name = "a"; param_mod = CopyMod;}] in
    let is_null_specs = spec_decl "is_null__"
        "case { a=null -> requires true ensures res ;
                a!=null -> requires true ensures !res;}"
        is_null_param_list Bool false in
    let count_param_list =
      [{param_type = Named "node"; param_name = "x"; param_mod = CopyMod;}] in
    let cstruc_form = spec_decl "count" "requires x::ll<n> ensures x::ll<n> & res=n;"
        count_param_list Int true in
    let lfe = init_ctx cstruc_form in
    (*
     {(boolean v_bool_46_2101;
     (v_bool_46_2101 = {is_null___$node(x)};
     if (v_bool_46_2101) [LABEL! 150,0: (int v_int_47_2092;
     (v_int_47_2092 = 0;
     ret# v_int_47_2092))]
     else [LABEL! 150,1: (int v_int_49_2100;
     (v_int_49_2100 = {((int v_int_49_2099;
     (v_int_49_2099 = 1;
     (int v_int_49_2098;
     v_int_49_2098 = {((node v_node_49_2096;
     v_node_49_2096 = bind x to (val_49_2093,next_49_2094) [read] in
     next_49_2094);
     count$node(v_node_49_2096) rec)})));
     add___$int~int(v_int_49_2099,v_int_49_2098))};
     ret# v_int_49_2100))]
     ))}
    *)
    let lfe = check_pre_post lfe is_null_specs ["x"] in
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Bool "v_bool_46_2101" in

    let then_lfe = add_cond_to_ctx lfe "v_bool_46_2101" true in
    let then_lfe = upd_result_with_int then_lfe 0 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_47_2092" in
    let then_lfe = upd_result_with_var then_lfe Int "v_int_47_2092" in

    let else_lfe = add_cond_to_ctx lfe "v_bool_46_2101" false in
    let else_lfe = upd_result_with_int else_lfe 1 in
    let else_lfe = add_assign_to_ctx else_lfe Int "v_int_49_2099" in
    let else_lfe = data_field_read else_lfe (Named "node") "x" "next" in
    (* let else_lfe = bind_data_to_names else_lfe (Named("node")) "x"
       [(Int, "val_49_2093"); (Named("node"), "next_49_2094")] true in *)
    (* let else_lfe = upd_result_with_var else_lfe (Named("node")) "next_49_2094" in *)
    let else_lfe = add_assign_to_ctx else_lfe (Named "node") "v_node_49_2096" in
    let else_lfe = check_pre_post else_lfe cstruc_form ["v_node_49_2096"] in
    let else_lfe = add_assign_to_ctx (Gen.unsome else_lfe) Int "v_int_49_2098" in
    let else_lfe = check_pre_post else_lfe add_specs
        ["v_int_49_2099"; "v_int_49_2098"] in
    let else_lfe = add_assign_to_ctx (Gen.unsome else_lfe) Int "v_int_49_2100" in
    let else_lfe = upd_result_with_var else_lfe Int "v_int_49_2100" in

    let lfe = disj_of_ctx then_lfe else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)))
  in

  let verify_4 () =
    let is_null_param_list =
      [{param_type = Named "node"; param_name = "a"; param_mod = CopyMod;}] in
    let is_null_specs = spec_decl "is_null__"
        "case { a=null -> requires true ensures res ;
                a!=null -> requires true ensures !res;}"
        is_null_param_list Bool false in
    (*
      {(boolean v_bool_36_2099;
        (v_bool_36_2099 = {((node v_node_36_2091;
        v_node_36_2091 = bind x to (val_36_2087,next_36_2088) [read] in
        next_36_2088);
        is_null___$node(v_node_36_2091))};
        if (v_bool_36_2099) [LABEL! 147,0: bind x to (val_37_2092,next_37_2093) [write] in
        next_37_2093 = y]
        else [LABEL! 147,1: {((node v_node_39_2098;
        v_node_39_2098 = bind x to (val_39_2094,next_39_2095) [read] in
        next_39_2095);
        append$node~node(v_node_39_2098,y) rec)}]
        ))}
    *)
    let param_list =
      [{param_type = Named "node"; param_name = "x"; param_mod = RefMod;};
       {param_type = Named "node"; param_name = "y"; param_mod = RefMod;}] in
    let cstruc_form = spec_decl "append" "requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;" param_list Void true in
    let lfe = init_ctx cstruc_form in

    let lfe = data_field_read lfe (Named "node") "x" "next" in
    (* let lfe = bind_data_to_names lfe (Named("node")) "x" [(Int, "val_36_2087");
       (Named("node"), "next_36_2088")] true in *)
    (* let lfe = upd_result_with_var lfe (Named("node")) "next_36_2088" in *)
    let lfe = add_assign_to_ctx lfe (Named "node") "v_node_36_2091" in
    let lfe = check_pre_post lfe is_null_specs ["v_node_36_2091"] in
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Bool "v_bool_36_2099" in

    let then_lfe = add_cond_to_ctx lfe "v_bool_36_2099" true in
    let then_lfe = data_field_update then_lfe (Named "node") "x" "next" "y" in
    (* let then_lfe = bind_data_to_names then_lfe (Named("node")) "x" [(Int, "val_37_2092");
       (Named("node"), "next_37_2093")] false in *)
    (* let then_lfe = upd_result_with_var then_lfe (Named("node")) "y" in *)
    (* let then_lfe = add_assign_to_ctx then_lfe (Named("node")) "next_37_2093" in *)
    (* let then_lfe = add_vheap_to_ctx then_lfe (Named("node")) "x" [(Int, "val_37_2092");
       (Named("node"), "next_37_2093")] false in *)
    
    let else_lfe = add_cond_to_ctx lfe "v_bool_36_2099" false in
    let else_lfe = data_field_read else_lfe (Named "node") "x" "next" in
    (* let else_lfe = bind_data_to_names else_lfe (Named("node")) "x" [(Int, "val_39_2094");
       (Named("node"), "next_39_2095")] true in *)
    (* let else_lfe = upd_result_with_var else_lfe (Named("node")) "next_39_2095" in *)
    let else_lfe = add_assign_to_ctx else_lfe (Named "node") "v_node_39_2098" in
    let else_lfe = check_pre_post else_lfe cstruc_form ["v_node_39_2098"; "y"] in
    let else_lfe = Gen.unsome else_lfe in

    let lfe = disj_of_ctx then_lfe else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)))
  in

  let verify_5 () =
    (* int foo (node i)
    requires i != null
    ensures res = 1;
    {
        if (i!=null) {
            return 1;
        }
        return 0;
    } *)
    (* {((boolean v_bool_10_2042;
    (v_bool_10_2042 = {is_not_null___$node(i)};
    if (v_bool_10_2042) [LABEL! 145,0: {(int v_int_11_2041;
    (v_int_11_2041 = 1;
    ret# v_int_11_2041))}]
    else [LABEL! 145,1: ]
    ));
    (int v_int_13_2043;
    (v_int_13_2043 = 0;
    ret# v_int_13_2043)))} *)
    let cstruc_form = spec_decl "foo" "requires i != null ensures res = 1;"
        [{param_type = Named "node"; param_name = "i"; param_mod = RefMod;}] Int
        false in
    let lfe = init_ctx cstruc_form in
    let lfe = check_pre_post_str lfe "is_not_null___$node" ["i"] in
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Bool "v_bool_10_2042" in

    (* Cond : then branch *)
    let then_lfe = add_cond_to_ctx lfe "v_bool_10_2042" true in
    let then_lfe = upd_result_with_int then_lfe 1 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_6_2018" in
    let then_lfe = upd_result_with_var then_lfe Int "v_int_6_2018" in
    (* Cond : else branch *)
    let else_lfe = add_cond_to_ctx lfe "v_bool_10_2042" false in
    let else_lfe = upd_result_with_int else_lfe 0 in
    let else_lfe = add_assign_to_ctx else_lfe Int "v_int_8_2019" in
    let else_lfe = upd_result_with_var else_lfe Int "v_int_8_2019" in

    let lfe = disj_of_ctx then_lfe else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form))) in

  let verify_6 () =
    (*
     {(node v_node_10_2062;
     (v_node_10_2062 = {((null_type v_null_type_10_2061;
     v_null_type_10_2061 = null);
     new node(val,v_null_type_10_2061))};
     ret# v_node_10_2062))}
    *)
    let param_list = [{param_type = Int; param_name = "val"; param_mod = RefMod;}] in
    let cstruc_form = spec_decl "init_node" "requires true ensures res::node<val,_>;"
        param_list (Named "node") false in
    let lfe = init_ctx cstruc_form in

    let lfe = upd_result_with_null lfe in
    let lfe = add_assign_to_ctx lfe Null "v_null_type_10_2061" in
    let lfe = add_heap_node_to_ctx lfe (Named "node") ["val"; "v_null_type_10_2061"] in
    let lfe = add_assign_to_ctx lfe (Named "node") "v_node_10_2061" in
    let lfe = upd_result_with_var lfe (Named "node") "v_node_10_2061" in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)))
  in

  let verify_7 () =
    let gt_param_list = [{param_type = Int; param_name = "a"; param_mod = NoMod;};
                         {param_type = Int; param_name = "b"; param_mod = NoMod;}] in
    let gt_specs = spec_decl "gt___int" "case { a >  b -> ensures  res;
                                                a <= b -> ensures !res;};"
        gt_param_list Bool false in
    let add_param_list = [{param_type = Int; param_name = "a"; param_mod = NoMod;};
                          {param_type = Int; param_name = "b"; param_mod = NoMod;}] in
    let add_specs = spec_decl "add__" "requires true ensures res = a + b;"
        add_param_list Int false in
    (*
     {(boolean v_bool_46_2099;
     (v_bool_46_2099 = {((int v_int_46_2096;
     v_int_46_2096 = 0);
     gt___$int~int(i,v_int_46_2096))};
     if (v_bool_46_2099) [LABEL! 156,0: {i = {((int v_int_47_2098;
     v_int_47_2098 = 1);
     add___$int~int(i,v_int_47_2098))}}]
     else [LABEL! 156,1: ]
     ))}
    *)
    let param_list = [{param_type = Int; param_name = "i"; param_mod = RefMod;}] in
    let cstruc_form = spec_decl "foo" "case {
          i > 0 -> requires true ensures i' = i + 1;
          i <= 0 -> requires true ensures i' = i;};" param_list Void false in
    let lfe = init_ctx cstruc_form in
    let lfe = upd_result_with_int lfe 0 in
    let lfe = add_assign_to_ctx lfe Int "v_int_46_2096" in
    let lfe = Gen.unsome (check_pre_post lfe gt_specs ["i"; "v_int_46_2096"]) in
    let lfe = add_assign_to_ctx lfe Bool "v_bool_46_2099" in

    let then_lfe = add_cond_to_ctx lfe "v_bool_46_2099" true in
    let then_lfe = upd_result_with_int then_lfe 1 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_47_2098" in
    let then_lfe = Gen.unsome (check_pre_post then_lfe add_specs 
                                 ["i"; "v_int_47_2098"]) in
    let then_lfe = add_assign_to_ctx then_lfe Int "i" in

    let else_lfe = add_cond_to_ctx lfe "v_bool_46_2099" false in

    let lfe = disj_of_ctx then_lfe else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)));
  in

  let verify_8 () =
    (* void fun(ref int i)
      requires i<10
      ensures i'=10;
    {
      while(i<10)
        requires true
        ensures i<10 & i'=10
          or i>=10 & i'=i;
      {
        i=i+1;
      }
    } *)
    (* {(boolean v_bool_5_2040;
    (v_bool_5_2040 = {((int v_int_5_2034;
    v_int_5_2034 = 10);
    lt___$int~int(i,v_int_5_2034))};
    if (v_bool_5_2040) [{({i = {((int v_int_10_2037;
    v_int_10_2037 = 1);
    add___$int~int(i,v_int_10_2037))}};
    {while_5_2$int(i) rec})}]
    else []
    ))} *)
    let param_list = [{param_type = Int; param_name = "i"; param_mod = RefMod;}] in
    let cstruc_form = spec_decl "while_5_2" "requires true
        ensures i<10 & i'=10
          or i>=10 & i'=i;"
      param_list Void true in
    let lfe = init_ctx cstruc_form in
    let lfe = upd_result_with_int lfe 10 in
    let lfe = add_assign_to_ctx lfe Int "v_int_5_2034" in
    let lfe = check_pre_post_str lfe "lt___$int~int" ["i"; "v_int_5_2034"] in
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Bool "v_bool_10_2040" in

    (* Cond : then branch *)
    let then_lfe = add_cond_to_ctx lfe "v_bool_10_2040" true in
    let then_lfe = upd_result_with_int then_lfe 1 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_10_2037" in
    let then_lfe = check_pre_post_str then_lfe "add___$int~int"
        ["i"; "v_int_5_2037"] in
    let then_lfe = check_pre_post (Gen.unsome then_lfe) cstruc_form ["i"] in
    (* Cond : else branch *)
    let else_lfe = add_cond_to_ctx lfe "v_bool_10_2040" false in

    let lfe = disj_of_ctx (Gen.unsome then_lfe) else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)))
  in

  let verify_9 () =
    let param_list = [{param_type = Int; param_name = "m"; param_mod = NoMod;};
                      {param_type = Int; param_name = "n"; param_mod = NoMod;}] in
    let cstruc_form = spec_decl "gcd"
        "case {
               m=n -> requires MayLoop ensures res=m;
               m!=n ->
                       case {
                             m <= 0 -> requires MayLoop ensures false;
                             m > 0 ->
                                      case {
                                            n <= 0 -> requires MayLoop ensures false;
                                            n > 0 -> requires MayLoop ensures res>0;
                                           }
                            }
              }" param_list Int true in
    let lfe = init_ctx cstruc_form in
    let lfe = Gen.unsome (check_pre_post_str lfe "eq___$int~int" ["m"; "n"]) in
    let lfe = add_assign_to_ctx lfe Bool "v_bool_20_2055" in

    let then_lfe = add_cond_to_ctx lfe "v_bool_20_2055" true in
    let then_lfe = upd_result_with_var then_lfe Int "m" in

    let else_lfe = add_cond_to_ctx lfe "v_bool_20_2055" false in
    let else_lfe = Gen.unsome (check_pre_post_str else_lfe "gt___$int~int"
                                 ["m"; "n"]) in
    let else_lfe = add_assign_to_ctx else_lfe Bool "v_bool_21_2054" in

    let then_lfe2 = add_cond_to_ctx else_lfe "v_bool_21_2054" true in
    let then_lfe2 = Gen.unsome (check_pre_post_str then_lfe2 "minus___$int~int"
                                  ["m"; "n"]) in
    let then_lfe2 = add_assign_to_ctx then_lfe2 Int "v_int_21_2046" in
    let then_lfe2 = Gen.unsome (check_pre_post then_lfe2 cstruc_form
                                  ["v_int_21_2046"; "n"]) in
    let then_lfe2 = add_assign_to_ctx then_lfe2 Int "v_int_21_2047" in
    let then_lfe2 = upd_result_with_var then_lfe2 Int "v_int_21_2047" in

    let else_lfe2 = add_cond_to_ctx else_lfe "v_bool_21_2054" false in
    let else_lfe2 = Gen.unsome (check_pre_post_str else_lfe2 "minus___$int~int"
                                  ["n"; "m"]) in
    let else_lfe2 = add_assign_to_ctx else_lfe2 Int "v_int_22_2052" in
    let else_lfe2 = Gen.unsome (check_pre_post else_lfe2 cstruc_form
                                  ["m"; "v_int_22_2052"]) in
    let else_lfe2 = add_assign_to_ctx else_lfe2 Int "v_int_22_2053" in
    let else_lfe2 = upd_result_with_var else_lfe2 Int "v_int_22_2053" in

    let else_lfe = disj_of_ctx then_lfe2 else_lfe2 in
    let lfe = disj_of_ctx then_lfe else_lfe in

    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form)))
  in

  verify_1 ();
  [%expect{| true |}];
  verify_2 ();
  [%expect{| true |}];
  verify_3 ();
  [%expect{| true |}];
  verify_4 ();
  [%expect{| true |}];
  verify_5 ();
  [%expect{| true |}];
  verify_6 ();
  [%expect{| true |}];
  verify_7 ();
  [%expect{| true |}];
  verify_8 ();
  [%expect{| true |}];
  verify_9 ();
  [%expect{| true |}]


