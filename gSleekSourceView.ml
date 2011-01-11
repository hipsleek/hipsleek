(***********************
 * Sleek source view
 * Derived from GSourceView2
 ***********************)

module SU = GUtil.SourceUtil

class sleek_source_view ?(text = "") () =

  let get_sleek_lang () =
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    match language_manager#guess_language ~content_type:lang_mime_type () with
    | None -> failwith ("no language for " ^ lang_mime_type)
    | Some lang -> lang
  in
  let tag_name = "checkentail" in
  let font_name = "Monospace 11" in

  object (self)
    val delegate = GSourceView2.source_view ()
    
    initializer
      delegate#set_show_line_numbers true;
      delegate#set_auto_indent true;
      delegate#set_tab_width 2;
      delegate#set_insert_spaces_instead_of_tabs true;
      delegate#misc#modify_font_by_name font_name;
      delegate#set_show_line_marks true;
      let buffer = delegate#source_buffer in
      buffer#set_language (Some (get_sleek_lang ()));
      buffer#set_text text;
      buffer#set_highlight_syntax true;
      ignore (buffer#create_tag ~name:tag_name [`BACKGROUND "light blue"]);
      (*ignore (buffer#connect#mark_set *)
        (*~callback:(fun _ _ -> highlight_selected_word ()))*)

    method coerce = delegate#coerce
    method source_buffer = delegate#source_buffer

    (* highlight checkentail command
     * by applying checkentail tag on that part of source code *)
    method hl_entailment (e: SU.entailment): unit =
      self#clear_highlight ();
      let start = self#source_buffer#get_iter_at_char e.SU.start_char in
      let stop = self#source_buffer#get_iter_at_char e.SU.stop_char in
      self#source_buffer#apply_tag_by_name tag_name start stop

    (* highlight all checkentail commands *)
    method hl_all_entailement () : unit =
      let hl (e: SU.entailment) : unit =
        let start = self#source_buffer#get_iter_at_char e.SU.start_char in
        let stop = self#source_buffer#get_iter_at_char e.SU.stop_char in
        self#source_buffer#apply_tag_by_name tag_name start stop
      in
      let src = self#source_buffer#get_text () in
      let e_list = SU.parse_entailment_list src in
      List.iter hl e_list

    (* clear current highlight
     * by removing checkentail tag in current source code *)
    method clear_highlight () =
      let start = self#source_buffer#get_iter `START in
      let stop = self#source_buffer#get_iter `END in
      self#source_buffer#remove_tag_by_name tag_name start stop

    (*
     *method highlight_selected_word () =
     *  let start = self#source_buffer#get_iter_at_mark `SEL_BOUND in
     *  let stop = self#source_buffer#get_iter_at_mark `INSERT in
     *  let word = self#source_buffer#get_text ~start ~stop () in
     *  print word
     *)

  end

