open SBLib
open SBGlobals
open SBCast

module DB = SBDebug

type templ_kind =
  | LinearT
  | EqArithT
  | EqPtrT
  | NePtrT
  | ConjT of int
  | EqArithConjT of int
  | EqPtrConjT of int
  | IncrT of (templ_kind * int)

type func_templ_kind =
  | ArithExpT

let pr_func_tk = function
  | ArithExpT -> "ArithExpT"

let rec pr_tk = function
  | LinearT -> "LinearT"
  | EqArithT -> "EqArithT"
  | EqPtrT -> "EqPtrT"
  | NePtrT -> "NePtrT"
  | ConjT n -> "ConjT " ^ (string_of_int n)
  | EqArithConjT n -> "EqArithConjT " ^ (string_of_int n)
  | EqPtrConjT n -> "EqPtrConjT " ^ (string_of_int n)
  | IncrT tk -> "IncrT" ^ (pr_pair pr_tk string_of_int tk)

let pr_unk_coes_conj uc =
  "[" ^ (pr_list pr_var (uc.uc_param_coes @ uc.uc_base_coes)) ^ "]"

let pr_unk_coes_rel unk =
  unk.uc_name ^ "(" ^
    (pr_list pr_unk_coes_conj unk.uc_coes_conjs) ^ ")"

let is_neq_ptr_tk = function
  | NePtrT -> true | _ -> false

let rec is_eq_tk = function
  | EqArithT | EqArithConjT _
  | EqPtrT | EqPtrConjT _ -> true
  | IncrT (tk, _) -> is_eq_tk tk
  | _ -> false

let rec is_ptr_tk = function
  | EqPtrT | NePtrT | EqPtrConjT _ -> true
  | IncrT (tk, _) -> is_ptr_tk tk
  | _ -> false

let is_incr_tk = function
  | IncrT _ -> true | _ -> false

let is_conj_tk = function
  | ConjT n
  | EqArithConjT n
  | EqPtrConjT n -> n >= 2
  | _ -> false

let rec downgrade_tk tk =
  match tk with
  | EqArithT -> LinearT
  | EqPtrT -> NePtrT
  | IncrT (tk, _) -> downgrade_tk tk
  | _ -> tk

let mk_incr_tk tk =
  match tk with
  | IncrT (tk, i) -> IncrT(tk, i + 1)
  | _ -> IncrT (tk, 0)

let get_incr_num_tk = function
  | IncrT (_, i) -> i
  | _ -> -1

let get_unk_param_coes_conj unk =
  List.map (fun uc -> uc.uc_param_coes) unk.uc_coes_conjs

let get_unk_param_coes unk =
  unk |> get_unk_param_coes_conj |> List.concat

let get_unk_base_coes unk =
  List.map (fun uc -> uc.uc_base_coes) unk.uc_coes_conjs |> List.concat

let get_all_unk_coes unk =
  (get_unk_param_coes unk) @ (get_unk_base_coes unk)

let dedup_unk_coes_rels =
  dedup_gen (fun u1 u2 -> eq_s u1.uc_name u2.uc_name)

(* Returns a list of unknown coefficients and its base *)
let get_unk_coes_rel_defn (rel: rel_defn): unk_coes_rel option =
  match rel.rel_body with
  | RbForm _ -> None
  | RbUnknown -> None
  | RbTemplate tmpl -> Some tmpl.templ_unk_coes

let get_unk_coes_func_defn (func: func_defn): unk_coes_rel option =
  match func.func_body with
  | FuncForm _ -> None
  | FuncUnknown -> None
  | FuncTemplate tmpl -> Some tmpl.func_templ_unk_coes

let get_unk_coes_pf (prog: program) (f: pure_form): unk_coes_rel list =
  f |> find_rel_defn_pf prog.prog_rels |>
  List.fold_left (fun acc r ->
    match (get_unk_coes_rel_defn r) with
    | None -> acc | Some u -> acc @ [u]) []

let get_unk_coes_pf_funcs (prog: program) (f: pure_form): unk_coes_rel list =
  f |> find_func_defn_pf prog.prog_funcs |>
  List.fold_left (fun acc r ->
    match (get_unk_coes_func_defn r) with
    | None -> acc | Some u -> acc @ [u]) []

let get_unk_coes_pf (prog: program) (f: pure_form): unk_coes_rel list =
  DB.trace_1 "get_unk_coes_pf" (pr_pf, pr_list pr_unk_coes_rel) f
    (fun () -> get_unk_coes_pf prog f)

let split_unk_coes_pf (prog: program) (f: pure_form): var list * var list =
  get_unk_coes_pf prog f |>
  List.map (fun unk -> unk.uc_coes_conjs) |> List.concat |>
  List.map (fun uc ->
    (uc.uc_param_coes @ uc.uc_base_coes, uc.uc_base_coes)) |>
  List.split |> Pair.map List.concat

let rec mk_list n f args =
  if (n == 0) then []
  else (mk_list (n-1) f args) @ [(f n args)]

class counter = object(self)
  val mutable cnt = -1
  method inc_and_get = cnt <- cnt + 1; cnt
  method reset = cnt <- -1
  method get_name prefix =
    let i = self # inc_and_get in
    prefix ^ "_" ^ (string_of_int i)
end

class virtual ['t] template = object(self)
  method virtual get_form: 't -> pure_form

  method virtual get_unk_coes: 't -> unk_coes_rel

  method virtual mk_templ: rel_defn -> 't

  method mk_rel_body (rel: rel_defn): rel_body_form =
    let templ = self # mk_templ rel in
    RbTemplate { templ_unk_coes = self # get_unk_coes templ;
                 templ_body = self # get_form templ;
                 templ_dummy = false }

  method update_pure_entail (prog: program) (pent: pure_entail): pure_entail =
    { pent with
      pent_lhs = unfold_rform_pf prog.prog_rels pent.pent_lhs;
      pent_rhs = unfold_rform_pf prog.prog_rels  pent.pent_rhs; }

  method update_rel_defn (tk: templ_kind) (prog: program)
      (unk_rel_names: string list): program =
    let rels = prog.prog_rels in
    let new_rels = List.map (fun rel ->
      let new_body =
        if ((mem_ss rel.rel_name unk_rel_names) &&
            ((is_incr_tk tk) || (is_template_rdefn rel)))
        then self # mk_rel_body rel
        else rel.rel_body
      in
      { rel with rel_body = new_body }) rels
    in { prog with prog_rels = new_rels }
end

class virtual ['t] func_template = object(self)
  method virtual get_form: 't -> exp

  method virtual get_unk_coes: 't -> unk_coes_rel

  method virtual mk_func_templ: func_defn -> 't

  method mk_func_body (func: func_defn): func_body_form =
    let templ = self # mk_func_templ func in
    FuncTemplate { func_templ_unk_coes = self # get_unk_coes templ;
                 func_templ_body = self # get_form templ;
                 func_templ_dummy = false }

  method update_pure_entail (prog: program) (pent: pure_entail): pure_entail =
    { pent with
      pent_lhs = unfold_rform_pf prog.prog_rels pent.pent_lhs;
      pent_rhs = unfold_rform_pf prog.prog_rels  pent.pent_rhs; }

  method update_func_defn (tk: func_templ_kind) (prog: program)
      (unk_rel_names: string list): program =
    let funcs = prog.prog_funcs in
    let new_funcs = List.map (fun func ->
      let new_body =
        let b = (mem_ss func.func_name unk_rel_names) &&
                (is_template_fdefn func) in
          let () = DB.nhprint "bool 188: " (string_of_bool) b in
        if ((mem_ss func.func_name unk_rel_names) &&
            (is_template_fdefn func))
        then self # mk_func_body func
        else func.func_body
      in
      { func with func_body = new_body }) funcs
    in { prog with prog_funcs = new_funcs }
end

module DummyTempl = struct
  type t = pure_form

  class templ = object
    inherit [t] template

    method get_form templ = templ

    method get_unk_coes _ = {
      uc_name = "";
      uc_coes_conjs = []; }

    method mk_templ _ = mk_true no_pos
  end
end

module DummyFuncTempl = struct
  type t = exp

  class func_templ = object
    inherit [t] func_template

    method get_form func_templ = func_templ

    method get_unk_coes _ = {
      uc_name = "";
      uc_coes_conjs = []; }

    method mk_func_templ _ = mk_null no_pos
  end
end

module ConjTempl = struct
  type t = {
    rname: string;
    unk_coes: unk_coes_conj list;
    form: pure_form;
  }

  class templ nconjs = object(self)
    inherit [t] template

    val mutable unk_coes = []

    method add_unk_coes uc =
      unk_coes <- unk_coes @ [uc]

    method reset_unk_coes =
      unk_coes <- []

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = templ.unk_coes; }

    method get_form templ = templ.form

    method mk_base_templ i name params =
      let cnt = new counter in
      let coe_prefix = name ^ "_c_" ^ (string_of_int i) in
      let base_coe = mk_var (cnt # get_name coe_prefix) TInt in
      let param_coes = List.map
          (fun _ -> mk_var (cnt # get_name coe_prefix) TInt) params in
      let unk_coes = {
        uc_param_coes = param_coes; uc_base_coes = [base_coe] } in
      let unk_exp =
        List.combine
          (List.map mk_exp_var param_coes)
          (List.map mk_exp_var params) |>
        List.fold_left (fun s (c, p) -> mk_bin_op Mul c p |>
                                        mk_bin_op Add s)
          (mk_exp_var base_coe)
      in
      let () = self # add_unk_coes unk_coes in
      let form = mk_bin_rel Ge unk_exp (mk_iconst 0) in
      form

    method mk_templ rel =
      let name, params = rel.rel_name, rel.rel_params in
      let () = self # reset_unk_coes in
      let form =
        if (nconjs <= 0) then
          mk_true no_pos
        else if (nconjs == 1) then
          self # mk_base_templ nconjs name params
        else
          (mk_list nconjs (fun i params ->
             self # mk_base_templ i name params) params) |>
          mk_pconj
      in
      { rname = name; unk_coes = unk_coes; form = form; }
  end
end


module LinearTempl = struct
  type t = {
    rname: string;
    unk_coe: unk_coes_conj;
    form: pure_form;
  }

  class templ = object
    inherit [t] template

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = [templ.unk_coe]; }

    method get_form templ = templ.form

    method mk_templ rel =
      let conj_templ = new ConjTempl.templ 1 in
      let t = conj_templ # mk_templ rel in
      { rname = rel.rel_name;
        unk_coe = List.hd t.ConjTempl.unk_coes;
        form = t.ConjTempl.form; }
  end
end

module EqArithConjTempl = struct
  type t = {
    rname: string;
    unk_coes: unk_coes_conj list;
    form: pure_form;
  }

  class templ nconjs = object(self)
    inherit [t] template

    val mutable unk_coes = []

    method add_unk_coes uc =
      unk_coes <- unk_coes @ [uc]

    method reset_unk_coes =
      unk_coes <- []

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = templ.unk_coes; }

    method get_form templ = templ.form

    method mk_base_templ i name params =
      let cnt = new counter in
      let coe_prefix = name ^ "_c_" ^ (string_of_int i) in
      let base_coe = mk_var (cnt # get_name coe_prefix) TInt in
      let param_coes = List.map
          (fun _ -> mk_var (cnt # get_name coe_prefix) TInt) params in
      let unk_coes = {
        uc_param_coes = param_coes; uc_base_coes = [base_coe] } in
      let unk_exp =
        List.combine
          (List.map mk_exp_var param_coes)
          (List.map mk_exp_var params) |>
        List.fold_left (fun s (c, p) -> mk_bin_op Mul c p |>
                                        mk_bin_op Add s)
          (mk_exp_var base_coe)
      in
      let () = self # add_unk_coes unk_coes in
      let form = mk_bin_rel Eq unk_exp (mk_iconst 0) in
      form

    method mk_templ rel =
      let name, params = rel.rel_name, rel.rel_params in
      let () = self # reset_unk_coes in
      let form =
        if (nconjs <= 0) then
          mk_true no_pos
        else if (nconjs == 1) then
          self # mk_base_templ nconjs name params
        else
          (mk_list nconjs (fun i params ->
             self # mk_base_templ i name params) params) |>
          mk_pconj
      in
      { rname = name; unk_coes = unk_coes; form = form; }
  end
end

module EqArithTempl = struct
  type t = {
    rname: string;
    unk_coe: unk_coes_conj;
    form: pure_form;
  }

  class templ = object
    inherit [t] template

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = [templ.unk_coe]; }

    method get_form templ = templ.form

    method mk_templ rel =
      let conj_templ = new EqArithConjTempl.templ 1 in
      let t = conj_templ # mk_templ rel in
      { rname = rel.rel_name;
        unk_coe = List.hd t.EqArithConjTempl.unk_coes;
        form = t.EqArithConjTempl.form; }
  end
end

module ArithExpTempl = struct
  type t = {
    fname: string;
    unk_coe: unk_coes_conj;
    form: exp;
  }

  class func_templ = object
    inherit [t] func_template

    method get_form func_templ = func_templ.form
    method get_unk_coes templ =
      {
        uc_name = templ.fname;
        uc_coes_conjs = [templ.unk_coe];
      }

    method mk_func_templ func_defn =
      let mk_base_templ name params =
        let cnt = new counter in
        let coe_prefix = name ^ "_c_" in
        let base_coe = mk_var (cnt # get_name coe_prefix) TInt in
        let param_coes = List.map
                           (fun _ -> mk_var (cnt # get_name coe_prefix) TInt) params in
        let unk_coes = {
          uc_param_coes = param_coes; uc_base_coes = [base_coe] } in
        let unk_exp =
          List.combine
            (List.map mk_exp_var param_coes)
            (List.map mk_exp_var params) |>
          List.fold_left (fun s (c, p) -> mk_bin_op Mul c p |>
                                          mk_bin_op Add s)
            (mk_exp_var base_coe)
        in
        (unk_exp, unk_coes)
      in
      let name, params = func_defn.func_name, func_defn.func_params in
      let (unk_exp, unk_coes) = mk_base_templ name params in
      {
        fname = func_defn.func_name;
        unk_coe = unk_coes;
        form = unk_exp;
      }
  end
end

module EqPtrConjTempl = struct
  type t = {
    rname: string;
    unk_coes: unk_coes_conj list;
    form: pure_form;
  }

  class templ nconjs = object(self)
    inherit [t] template

    val mutable unk_coes = []

    method add_unk_coes uc =
      unk_coes <- unk_coes @ [uc]

    method reset_unk_coes =
      unk_coes <- []

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = templ.unk_coes; }

    method get_form templ = templ.form

    method mk_base_templ i name params =
      let cnt = new counter in
      let coe_prefix = name ^ "_c_" ^ (string_of_int i) in
      let param_coes = List.map
          (fun _ -> mk_var (cnt # get_name coe_prefix) TInt) params in
      let unk_coes = {
        uc_param_coes = param_coes; uc_base_coes = [] } in
      let unk_exp =
        List.combine
          (List.map mk_exp_var param_coes)
          (List.map mk_exp_var params) |>
        List.fold_left (fun s (c, p) -> mk_bin_op Mul c p |>
                                        mk_bin_op Add s)
          (mk_iconst 0)
      in
      let () = self # add_unk_coes unk_coes in
      let form = mk_bin_rel Eq unk_exp (mk_iconst 0) in
      form

    method mk_templ rel =
      let name, params = rel.rel_name, rel.rel_params in
      let () = self # reset_unk_coes in
      let form =
        if (nconjs <= 0) then
          mk_true no_pos
        else if (nconjs == 1) then
          self # mk_base_templ nconjs name params
        else
          (mk_list nconjs (fun i params ->
             self # mk_base_templ i name params) params) |>
          mk_pconj
      in
      { rname = name; unk_coes = unk_coes; form = form; }
  end
end

module EqPtrTempl = struct
  type t = {
    rname: string;
    unk_coe: unk_coes_conj;
    form: pure_form;
  }

  class templ = object
    inherit [t] template

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = [templ.unk_coe]; }

    method get_form templ = templ.form

    method mk_templ rel =
      let name, params = rel.rel_name, rel.rel_params in
      let cnt = new counter in
      let coe_prefix = name ^ "_c" in
      let param_coes = List.map
          (fun _ -> mk_var (cnt # get_name coe_prefix) TInt) params in
      let unk_coes = {
        uc_param_coes = param_coes; uc_base_coes = [] } in
      let unk_exp =
        List.combine
          (List.map mk_exp_var param_coes)
          (List.map mk_exp_var params) |>
        List.fold_left (fun s (c, p) -> mk_bin_op Mul c p |>
                                        mk_bin_op Add s)
          (mk_iconst 0)
      in
      let f = mk_bin_rel Eq unk_exp (mk_iconst 0) in
      { rname = name; unk_coe = unk_coes; form = f; }
      (* let conj_templ = new EqPtrConjTempl.templ 1 in *)
      (* let t = conj_templ # mk_templ name params in *)
      (* { rname = name; *)
      (*   unk_coe = List.hd t.EqPtrConjTempl.unk_coes; *)
      (*   form = t.EqPtrConjTempl.form; } *)
  end
end

module NePtrTempl = struct
  type t = {
    rname: string;
    unk_coe: unk_coes_conj;
    form: pure_form;
  }

  class templ = object
    inherit [t] template

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = [templ.unk_coe]; }

    method get_form templ = templ.form

    method mk_templ rel =
      let name, params = rel.rel_name, rel.rel_params in
      let cnt = new counter in
      let coe_prefix = name ^ "_c" in
      let param_coes = List.map
          (fun _ -> mk_var (cnt # get_name coe_prefix) TInt) params in
      let unk_coes = {
        uc_param_coes = param_coes; uc_base_coes = [] } in
      let unk_exp =
        List.combine
          (List.map mk_exp_var param_coes)
          (List.map mk_exp_var params) |>
        List.fold_left (fun s (c, p) -> mk_bin_op Mul c p |>
                                        mk_bin_op Add s)
          (mk_iconst 0)
      in
      let f = mk_bin_rel Ne unk_exp (mk_iconst 0) in
      { rname = name; unk_coe = unk_coes; form = f; }
  end
end

module IncrTempl = struct
  type t = {
    rname: string;
    unk_coes: unk_coes_conj list;
    form: pure_form;
  }

  class templ (tk: templ_kind) = object
    inherit [t] template

    method get_unk_coes templ =
      { uc_name = templ.rname;
        uc_coes_conjs = templ.unk_coes; }

    method get_form templ = templ.form

    method mk_templ rel =
      let unk_coes, conj_f =
        match tk with
        | LinearT ->
          let tl = new LinearTempl.templ in
          let t = tl # mk_templ rel in
          tl # get_unk_coes t, tl # get_form t
        | EqArithT ->
          let tl = new EqArithTempl.templ in
          let t = tl # mk_templ rel in
          tl # get_unk_coes t, tl # get_form t
        | EqPtrT ->
          let tl = new EqPtrTempl.templ in
          let t = tl # mk_templ rel in
          tl # get_unk_coes t, tl # get_form t
        | NePtrT ->
          let tl = new NePtrTempl.templ in
          let t = tl # mk_templ rel in
          tl # get_unk_coes t, tl # get_form t
        | _ -> error ("IncrTempl: Unexpected atomic template kind")
      in
      let body_f = match rel.rel_body with
        | RbForm f -> f
        | RbUnknown -> error ("mk_templ: unknown relation: " ^ (pr_rd rel))
        | RbTemplate tmpl -> tmpl.templ_body
      in
      let () = DB.nhprint "body_f: " pr_pf body_f in
      let () = DB.nhprint "conj_f: " pr_pf conj_f in
      { rname = rel.rel_name;
        unk_coes = unk_coes.uc_coes_conjs;
        form = mk_pconj [body_f; conj_f]; }
  end
end


(***************************************)

let mk_rdefn_dummy ?(pos=no_pos) name params =
  let f_true = mk_true pos in
  let dummy_body = {
    templ_unk_coes = (new DummyTempl.templ) # get_unk_coes f_true;
    templ_body = f_true;
    templ_dummy = true; } in
  { rel_name = name;
    rel_params = params;
    rel_body = RbTemplate dummy_body;
    rel_pos = pos; }

let mk_fdefn_dummy ?(pos=no_pos) name params =
  let f_null = mk_null pos in
  let dummy_body = {
    func_templ_unk_coes = (new DummyFuncTempl.func_templ) # get_unk_coes f_null;
    func_templ_body = f_null;
    func_templ_dummy = true; } in
  { func_name = name;
    func_params = params;
    func_body = FuncTemplate dummy_body;
    func_pos = pos; }

let mk_rdefn_true ?(pos=no_pos) name params =
  { rel_name = name;
    rel_params = params;
    rel_body = RbForm (mk_true no_pos);
    rel_pos = pos; }
