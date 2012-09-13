open Globals
open Gen
open GUtil.SourceUtil

module CF = Cformula


let cols = new GTree.column_list
let col_name = cols#add Gobject.Data.string

class  ee_model  () =
object (self)
   val m_delegate = GTree.tree_store cols
     (*hash tbl path_id*leaves*)
   val m_hleaves = Hashtbl.create 20 (*((Gtk.tree_path, fail_explaining) Hashtbl.t;)*)
   val mutable m_verify_msg = ""

   initializer
   self#do_sth()

   method do_sth() = ()

   method coerce = m_delegate#coerce

   method get_iter path = m_delegate# get_iter path

   method get_path iter = m_delegate#get_path iter

   method set_verify_msg msg=
     let _ = m_verify_msg <- msg in
     ()

   method get_verify_msg (): string = m_verify_msg

   method get_selected_ft_by_path (path : Gtk.tree_path) =
     try
         Some (Hashtbl.find m_hleaves (GTree.Path.to_string path))
     with Not_found -> None

   method private process_append_errors (ft: CF.fail_type) (iter : Gtk.tree_iter):(string * CF.failure_kind) =
     let build_emsg emsg fk=
       emsg ^ "(" ^(Cprinter.string_of_failure_kind fk) ^ ")"
     in
     let to_path_string iter=
       GTree.Path.to_string (self#get_path iter)
     in
     match ft with
       | CF.Basic_Reason (fc , fe) ->
             (*this is a leaf, add into map*)
           let _ = Hashtbl.add m_hleaves (to_path_string iter) fe in
           (fc.CF.fc_message),fe.CF.fe_kind
       | CF.Trivial_Reason fe ->
             (*this is a leaf, add into map*)
           let _ = Hashtbl.add m_hleaves (to_path_string iter) fe in
           (build_emsg "Trivial " fe.CF.fe_kind),fe.CF.fe_kind
       | CF.Or_Reason (ft1, ft2) ->
           let _,fk1 = self#append_errors ft1 iter in
           let _,fk2 = self#append_errors ft2 iter in
           let fk = (CF.cmb_lor fk1 fk2) in
           (build_emsg "Join " fk),fk
       | CF.And_Reason (ft1, ft2) ->
           let _,fk1 = self#append_errors ft1 iter in
           let _,fk2 = self#append_errors ft2 iter in
           let fk = (CF.cmb_rand fk1 fk2) in
           (build_emsg "Compose " fk), fk
       | CF.Union_Reason (ft1, ft2) ->
           let _,fk1 = self#append_errors ft1 iter in
           let _,fk2 = self#append_errors ft2 iter in
           let fk = (CF.cmb_ror fk1 fk2) in
           (build_emsg "Search " fk), fk
       | CF.ContinuationErr _
       | CF.Or_Continuation _ -> report_error no_pos "geeview:append_errors"

   method private append_errors (ft: CF.fail_type) (p : Gtk.tree_iter):(string * CF.failure_kind) =
     let iter = m_delegate#append ~parent:p () in
     let err, fk = self#process_append_errors ft iter in
      m_delegate#set ~row:iter ~column:col_name err;
     err, fk

   method append_errors_tree (ft: CF.fail_type) =
     let _ = Hashtbl.clear m_hleaves in
     let toplevel = m_delegate#append () in
     let err, _ = self#process_append_errors ft toplevel in
     m_delegate#set ~row:toplevel ~column:col_name err;

end

class ee_view ?(model = new ee_model ()) () =
  object (self)
    val m_view = GTree.view ()
    val mutable m_model = model
    val m_name_col = GTree.view_column
      ~title:"status"
      ~renderer:(GTree.cell_renderer_text [], ["text", col_name])
      ()

    initializer
        m_view#selection#set_mode `SINGLE;
        m_name_col#set_resizable true;
        ignore (m_view#append_column m_name_col);
        ignore (m_view#set_expander_column (Some m_name_col));
        m_view#set_model (Some m_model#coerce)

    method coerce = m_view#coerce
    method selection = m_view#selection
    method misc = m_view#misc

    method set_model new_model =
      m_model <- new_model;
      m_view#set_model (Some m_model#coerce)

    method get_model (): ee_model = m_model

    method get_selected_ft () =
     let rows = self#selection#get_selected_rows in
     match rows with
        | [row] -> m_model#get_selected_ft_by_path row
        | _ -> None

    method get_selected_elocs () =
      let oft = self#get_selected_ft () in
      let elocs =
        match oft with
          | None -> let _ = print_endline "not a leaf" in []
          | Some fe ->
              let _ = print_endline "a leaf" in
              fe.CF.fe_locs
      in
      elocs

    method append_errors_tree (ft: CF.fail_type) =
      m_model#append_errors_tree ft
 end
