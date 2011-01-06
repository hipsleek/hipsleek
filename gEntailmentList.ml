
module SU = GUtil.SourceUtil

(**************************************
 * Entailment list model
 * Used for entailment list view below
 **************************************)
let cols = new GTree.column_list
let col_id = cols#add Gobject.Data.int
let col_line = cols#add Gobject.Data.int
let col_formula = cols#add Gobject.Data.string
let col_validity = cols#add Gobject.Data.string

class entailment_list_model ?(src = "") () =
  object (self)
    val delegate = GTree.list_store cols
    val mutable entailment_list = []
    val mutable modified_times = []
    val mutable count = 0

    initializer
      self#update_source src
    
    method coerce = delegate#coerce

    method append_one_entailment (e: SU.entailment) =
      let iter = delegate#append () in
      delegate#set ~row:iter ~column:col_id count;
      delegate#set ~row:iter ~column:col_line e.SU.start_line;
      delegate#set ~row:iter ~column:col_formula e.SU.formula;
      delegate#set ~row:iter ~column:col_validity "gtk-execute";
      count <- count + 1

    method update_source (src: string) =
      delegate#clear ();
      count <- 0;
      entailment_list <- SU.parse_entailment_list src;
      List.iter self#append_one_entailment entailment_list

    method get_entailment_by_path path =
      let row = delegate#get_iter path in
      let id = delegate#get ~row ~column:col_id in
      List.nth entailment_list id

    method set_entaiment_validity path (valid: bool) : unit =
      let row = delegate#get_iter path in
      let stock_id = self#stock_id_of_bool valid in
      delegate#set ~row ~column:col_validity stock_id

    method private stock_id_of_bool b =
      if b then "gtk-apply" else "gtk-cancel"

    method check_all (check_func: SU.entailment -> bool): unit =
      let func path iter =
        let entail = self#get_entailment_by_path path in
        let valid = check_func entail in
        self#set_entaiment_validity path valid;
        false
      in
      delegate#foreach func

    (*
     *method check_all (check_func: SU.entailment -> bool): unit =
     *  let output, input = Unix.pipe () in
     *  let func path iter =
     *    let _ = print_endline (string_of_int (Unix.getpid ())) in
     *    match Unix.fork () with
     *    | 0 -> begin [> child process <]
     *        let _ = print_endline (string_of_int (Unix.getpid ())) in
     *        let entail = self#get_entailment_by_path path in
     *        let valid = check_func entail in
     *        let res = if valid then "1" else "0" in
     *        ignore (Unix.write input res 0 1);
     *        Unix.close input;
     *        [>self#set_entaiment_validity path valid;<]
     *        exit 0
     *        [>true<]
     *      end
     *    | pid -> false
     *  in
     *  delegate#foreach func;
     *  let _ = try
     *      while true do
     *        ignore (Unix.wait ())
     *      done
     *    with Unix.Unix_error _ -> ()
     *  in 
     *  let buff = String.create 5 in
     *  ignore (Unix.read output buff 0 5);
     *  print_endline buff
     *)

  end


(*********************************
 * Entailment list view
 *********************************)
class entailment_list ?(model = new entailment_list_model ()) () =
  object (self)
    val view = GTree.view ()
    val mutable model = model
    val validity_col = GTree.view_column
      ~title:"Validity"
      ~renderer:(GTree.cell_renderer_pixbuf [], ["stock_id", col_validity])
      ()

    initializer
      view#selection#set_mode `SINGLE;
      let add_new_col title renderer =
        let col = GTree.view_column ~title ~renderer () in
        col#set_resizable true;
        ignore (view#append_column col);
        col
      in
      let text_renderer = GTree.cell_renderer_text [] in
      ignore (add_new_col "Line" (text_renderer, ["text", col_line]));
      ignore (add_new_col "Entailment" (text_renderer, ["text", col_formula]));
      validity_col#set_resizable true;
      validity_col#set_alignment 0.5;
      validity_col#set_clickable true;
      ignore (view#append_column validity_col);
      view#set_model (Some model#coerce)

    method coerce = view#coerce
    method selection = view#selection

    method set_model new_model =
      model <- new_model;
      view#set_model (Some model#coerce)

    method get_selected_entailment () =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] -> Some (model#get_entailment_by_path row)
      | _ -> None

    method set_selected_entailment_validity valid =
      let rows = self#selection#get_selected_rows in
      match rows with
      | [row] ->model#set_entaiment_validity row valid
      | _ -> ()

    method check_all (func: SU.entailment -> bool) : unit =
      model#check_all func

    method update_source (src: string) : unit =
      model#update_source src

    method set_checkall_handler callback =
      ignore (validity_col#connect#clicked ~callback)

  end

