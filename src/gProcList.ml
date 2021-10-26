#include "xdebug.cppo"
(**/**)
open GUtil.SourceUtil
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
class procedure_list_model ?(src = "") () =
  object (self)
    val delegate = GTree.list_store cols
    val mutable procedure_list = []
    val mutable error_postions = []
    val mutable count = 0
    val mutable source_digest = ""

    initializer
      self#update_source src

    method coerce = delegate#coerce
    method source_digest = source_digest

    method append_one_procedure (e: procedure) =
      let iter = delegate#append () in
      delegate#set ~row:iter ~column:col_id count;
      delegate#set ~row:iter ~column:col_line e.pos.start_line;
      delegate#set ~row:iter ~column:col_name e.name;
      delegate#set ~row:iter ~column:col_validity "gtk-execute";
      count <- count + 1

    method update_source ?(parse_func = parse_procedure_list) (src: string) =
      try begin
        procedure_list <- parse_func src;
        source_digest <- Digest.string src;
        error_postions <- [];
        delegate#clear ();
        count <- 0;
        List.iter self#append_one_procedure procedure_list
      end
      with Parsing.Parse_error -> ()

    method get_procedure_by_path path =
      let row = delegate#get_iter path in
      let id = delegate#get ~row ~column:col_id in
      List.nth procedure_list id

    method set_procedure_validity path (valid: bool) : unit =
      let row = delegate#get_iter path in
      let stock_id = self#stock_id_of_bool valid in
      delegate#set ~row ~column:col_validity stock_id

    method get_procedure_validity path : bool option =
      let row = delegate#get_iter path in
      let valid_string = delegate#get ~row ~column:col_validity in
      let res = 
        if valid_string = "gtk-yes" then Some true
        else if valid_string = "gtk-no" then Some false
        else None
      in res

    method private stock_id_of_bool b =
      if b then "gtk-yes" else "gtk-no"

    method check_all (check_func: procedure -> bool): unit =
      let func path iter =
        let entail = self#get_procedure_by_path path in
        let valid = check_func entail in
        self#set_procedure_validity path valid;
        false
      in
      delegate#foreach func

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

    method get_selected_procedure () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] -> Some (model#get_procedure_by_path row)
      | _ -> None

    method set_selected_procedure_validity valid =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] ->model#set_procedure_validity row valid
      | _ -> ()

    method get_selected_procedure_validity () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] -> model#get_procedure_validity row
      | _ -> None

    method check_all (func: procedure -> bool) : unit =
      model#check_all func

    method update_source (src: string) : unit =
      model#update_source src

    method set_checkall_handler callback =
      ignore (validity_col#connect#clicked ~callback)

  end

