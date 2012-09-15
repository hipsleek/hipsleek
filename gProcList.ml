(**/**)
open GUtil.SourceUtil

module EV = Geeview
(**/**)

(**/**)
let cols = new GTree.column_list
let col_id = cols#add Gobject.Data.int
let col_line = cols#add Gobject.Data.int
let col_name = cols#add Gobject.Data.string
let col_validity = cols#add Gobject.Data.string
(**/**)

(**
   Procedure list model
   Used for procedure list view below
 *)

type proc_ee = {
 proc_info: procedure;
 mutable proc_ee_msg: string;
 mutable proc_ee_model: EV.ee_model option;
}


class  procedure_list_model ?(src = "") () =
  object (self)
    val delegate = GTree.list_store cols
    val mutable m_procs = Hashtbl.create 20 (*proc_ee*)
    val mutable error_postions = []
    val mutable m_count = 0
    val mutable source_digest = ""
    val m_c_verify_unk = "gtk-execute"
    val m_c_verify_succ = "gtk-yes"
    val m_c_verify_fail = "gtk-no"

    initializer
      self#update_source src

    method coerce = delegate#coerce
    method source_digest = source_digest

    method get_delegate()=delegate

    method append_one_procedure (e: procedure) =
      let iter = delegate#append () in
      delegate#set ~row:iter ~column:col_id m_count;
      delegate#set ~row:iter ~column:col_line e.pos.start_line;
      delegate#set ~row:iter ~column:col_name e.name;
      delegate#set ~row:iter ~column:col_validity  m_c_verify_unk;
      let helper proc= {
          proc_info = proc;
          proc_ee_msg = "";
          proc_ee_model = None;
      } in
      let _ = Hashtbl.add m_procs m_count (helper e) in
      m_count <- m_count + 1


    method update_procedures iprocs cprocs (src: string) =
      let iproc_names = List.map (fun proc -> proc.Iast.proc_name) iprocs in
      let lprocs = get_procedure_list iproc_names cprocs in
      source_digest <- Digest.string src;
      error_postions <- [];
      delegate#clear ();
      m_count <- 0;
      (*update model view*)
      let _ = List.iter self#append_one_procedure lprocs in
      ()

    method update_source ?(parse_func = parse_procedure_list) (src: string) =
      let _ = Hashtbl.clear m_procs in
      m_count <- 0;
      delegate#clear ();
      try begin
          let lprocs =  parse_func src in
        source_digest <- Digest.string src;
        error_postions <- [];
        (*update model view*)
        let _ = List.iter self#append_one_procedure lprocs in
        ()
      end
      with Parsing.Parse_error -> ()

    method get_proc_by_path path =
      let row = delegate#get_iter path in
      let id = delegate#get ~row ~column:col_id in
      Hashtbl.find m_procs id

     method get_proc_info_by_path path =
       let proc = self#get_proc_by_path path in
       proc.proc_info

     method set_proc_ee_by_path path emsg emodel=
      let row = delegate#get_iter path in
      let id = delegate#get ~row ~column:col_id in
      let proc = Hashtbl.find m_procs id in
      let _ = proc.proc_ee_msg <- emsg in
      let _ = proc.proc_ee_model <- emodel in
      let _ = Hashtbl.replace m_procs id proc in
      ()

    method set_procedure_validity path (valid: bool) : unit =
      let row = delegate#get_iter path in
      let stock_id = self#stock_id_of_bool valid in
      delegate#set ~row ~column:col_validity stock_id

    method get_procedure_validity path : bool option =
      let row = delegate#get_iter path in
      let valid_string = delegate#get ~row ~column:col_validity in
      let res = 
        if valid_string =  m_c_verify_succ then Some true
        else if valid_string = m_c_verify_fail then Some false
        else None
      in res

    method private stock_id_of_bool b =
      if b then m_c_verify_succ else m_c_verify_fail

    method check_all (check_func: procedure -> bool) =
      (* let func path iter = *)
      (*   let proc = self#get_procedure_by_path path in *)
      (*   (\*check if path is verified?*\) *)
      (*   let res,onp = check_func proc in *)
      (*   self#set_procedure_validity path res; *)
      (*   let r = *)
      (*     match onp with *)
      (*       | Some np -> [np] *)
      (*       | None -> [] *)
      (*    in false *)
      (* in *)
      (* delegate#foreach func *)
      ()

    (* method verify_all (check_func: procedure -> bool) = *)
    (*   let func path iter = *)
    (*     (\*check if path is verified?*\) *)
    (*     let _ = *)
    (*       let v = self#get_procedure_validity in *)
    (*       if None then *)
    (*         let proc = self#get_proc_info_by_path path in *)
    (*         let res,onp = check_func proc in *)
    (*         self#set_procedure_validity path res; *)
    (*         let r = *)
    (*           match onp with *)
    (*             | Some np -> [np] *)
    (*             | None -> [] *)
    (*         in () *)
    (*     in false *)
    (*   in *)
    (*   delegate#foreach func *)
    (*   () *)

  end


(**
   procedure list view
 *)
class procedure_list ?(model = new procedure_list_model ()) () =
  object (self)
    val view = GTree.view ()
    val mutable model = model
    val line_col = GTree.view_column
      ~title:"Line"
      ~renderer:(GTree.cell_renderer_text [], ["text", col_line])
      ()
    val name_col = GTree.view_column
      ~title:"Procedure"
      ~renderer:(GTree.cell_renderer_text [], ["text", col_name])
      ()
    val validity_col = GTree.view_column
      ~title:"Validity"
      ~renderer:(GTree.cell_renderer_pixbuf [], ["stock_id", col_validity])
      ()

    initializer
      view#selection#set_mode `SINGLE;
      line_col#set_resizable true;
      name_col#set_resizable true;
      validity_col#set_resizable true;
      validity_col#set_alignment 0.5;
      validity_col#set_clickable true;
      ignore (view#append_column line_col);
      ignore (view#append_column name_col);
      ignore (view#append_column validity_col);
      view#set_model (Some model#coerce)

    method coerce = view#coerce
    method selection = view#selection
    method misc = view#misc
    method source_digest = model#source_digest

    method set_model new_model =
      model <- new_model;
      view#set_model (Some model#coerce)

    method get_model_delegate () = model#get_delegate()

    method get_selected_proc_info () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] -> Some (model#get_proc_info_by_path row)
      | _ -> None

    method get_proc_info_by_path path = model#get_proc_info_by_path path

    method get_selected_proc () =
      let rows = self#selection#get_selected_rows in
      match rows with
        | [row] -> Some (model#get_proc_by_path row)
        | _ -> None

    method set_selected_proc_ee emsg emodel=
      let rows = self#selection#get_selected_rows in
      match rows with
        | [row] -> (model#set_proc_ee_by_path row emsg emodel)
        | _ -> ()

    method set_proc_ee_by_path path emsg emodel=
      model#set_proc_ee_by_path path emsg emodel

    method set_selected_procedure_validity valid =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] ->model#set_procedure_validity row valid
      | _ -> ()

    method set_procedure_validity path valid = model#set_procedure_validity path valid

    method get_selected_procedure_validity () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] -> model#get_procedure_validity row
      | _ -> None

    method get_procedure_validity path = model#get_procedure_validity path

    (* method verify_all (func: procedure -> bool) : unit = *)
    (*   model#verify_all func *)

    method update_procedures iprocs cprocs (src: string) : unit =
      model#update_procedures iprocs cprocs src

    method update_procedures_from_txt (src: string) : unit =
      model#update_source src

    method set_checkall_handler callback =
      ignore (validity_col#connect#clicked ~callback)

  end

