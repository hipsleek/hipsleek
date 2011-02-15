(**
   Extended source view
 *)

open GUtil
open SourceUtil

class source_view ?(text = "") () =

  let tag_highlight = "highlight" in
  let tag_error = "error" in
  let font_name = "Monospace 11" in

  object (self)
    val delegate = GSourceView2.source_view ()
    val panel = GPack.vbox ()
    val status_lbl = GMisc.label ~show:false ~ypad:2 ()
    
    initializer
      status_lbl#set_use_markup true;
      delegate#set_show_line_numbers true;
      delegate#set_auto_indent true;
      delegate#set_tab_width 2;
      delegate#set_insert_spaces_instead_of_tabs true;
      delegate#misc#modify_font_by_name font_name;
      delegate#set_show_line_marks true;
      let buffer = delegate#source_buffer in
      buffer#set_text text;
      panel#pack status_lbl#coerce;
      panel#pack ~expand:true (create_scrolled_win delegate)#coerce;
      ignore (buffer#create_tag ~name:tag_highlight [`BACKGROUND "light blue"]);
      ignore (buffer#create_tag ~name:tag_error [`BACKGROUND "red"]);
      (*ignore (buffer#connect#mark_set *)
        (*~callback:(fun _ _ -> highlight_selected_word ()))*)

    method coerce = panel#coerce
    method connect = delegate#connect
    method event = delegate#event
    method source_buffer = delegate#source_buffer

    method private set_status (msg: string) =
      status_lbl#misc#show ();
      status_lbl#set_label msg

    method clear_status () =
      status_lbl#misc#hide ();
      status_lbl#set_label ""

    method private apply_tag (tag: string) (pos: seg_pos) =
      let start = self#source_buffer#get_iter_at_char pos.start_char in
      let stop = self#source_buffer#get_iter_at_char pos.stop_char in
      self#source_buffer#apply_tag_by_name tag start stop

    (** highlight part of the source and scroll to it if needed
       by applying checkentail tag on that part of source code *)
    method hl_segment ?(clear_previous_highlight = false) ?(scroll = false) (pos: seg_pos) =
      if clear_previous_highlight then self#clear_highlight ();
      self#apply_tag tag_highlight pos;
      if scroll then self#scroll_to_pos pos

    method hl_error ?(msg = "Error in source document") (pos: seg_pos) =
      let msg = Printf.sprintf "<b>%s</b>" msg in
      self#set_status msg;
      self#apply_tag tag_error pos;
      self#scroll_to_pos pos

    (** clear current highlight
       by removing checkentail tag in current source code *)
    method clear_highlight () =
      let start = self#source_buffer#get_iter `START in
      let stop = self#source_buffer#get_iter `END in
      self#source_buffer#remove_tag_by_name tag_highlight start stop;
      self#source_buffer#remove_tag_by_name tag_error start stop

    (** scroll the view window to given position *)
    method scroll_to_pos (pos: seg_pos) =
      let iter = self#source_buffer#get_iter_at_char pos.start_char in
      ignore (delegate#scroll_to_iter
        ~use_align:true ~yalign:0.5 iter)

    (*
     *method highlight_selected_word () =
     *  let start = self#source_buffer#get_iter_at_mark `SEL_BOUND in
     *  let stop = self#source_buffer#get_iter_at_mark `INSERT in
     *  let word = self#source_buffer#get_text ~start ~stop () in
     *  print word
     *)

  end

