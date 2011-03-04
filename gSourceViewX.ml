(**
   Extended source view
 *)

open GUtil
open SourceUtil

class source_view ?(text = "") () =

  let error = "error" in
  let highlight = "highlight" in
  let font_name = "Monospace 11" in

  object (self)
    val delegate = GSourceView2.source_view ()
    val panel = GPack.vbox ()
    val status_lbl = GMisc.label ~show:false ~ypad:2 ()
    
    initializer
      status_lbl#set_use_markup true;
      delegate#set_show_line_numbers true;
      delegate#set_auto_indent true;
      delegate#set_tab_width 4;
      delegate#set_insert_spaces_instead_of_tabs true;
      delegate#misc#modify_font_by_name font_name;
      delegate#set_show_line_marks true;
      let buffer = delegate#source_buffer in
      buffer#set_text text;
      panel#pack status_lbl#coerce;
      panel#pack ~expand:true (create_scrolled_win delegate)#coerce;
      delegate#set_mark_category_background ~category:highlight (Some (GDraw.color (`NAME "light gray")));
      delegate#set_mark_category_background ~category:error (Some (GDraw.color (`NAME "red")));
      let pixbuf =  delegate#misc#render_icon ~size:`DIALOG `DIALOG_INFO in
      delegate#set_mark_category_pixbuf ~category:highlight (Some pixbuf);
      let pixbuf =  delegate#misc#render_icon ~size:`DIALOG `DIALOG_ERROR in
      delegate#set_mark_category_pixbuf ~category:error (Some pixbuf);
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

    method private create_mark (category: string) (pos: seg_pos) =
      let start = self#source_buffer#get_iter_at_char pos.start_char in
      ignore (self#source_buffer#create_source_mark ~category start)

    (** highlight part of the source and scroll to it *)
    method hl_segment ?(clear_previous_highlight = false) ?(scroll = false) (pos: seg_pos) =
      if clear_previous_highlight then self#clear_highlight ();
      self#create_mark highlight pos;
      if scroll then self#scroll_to_pos pos

    method hl_error ?(msg = "Error in source document") (pos: seg_pos) =
      self#create_mark error pos;
      self#scroll_to_pos pos;
      let msg = Printf.sprintf "<b>%s</b>" msg in
      self#set_status msg

    (** clear current highlight
       by removing checkentail tag in current source code *)
    method clear_highlight () =
      let start = self#source_buffer#get_iter `START in
      let stop = self#source_buffer#get_iter `END in
      self#source_buffer#remove_source_marks ~category:error ~start ~stop ();
      self#source_buffer#remove_source_marks ~category:highlight ~start ~stop ();

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


(**
   Sleek source view
 *)
class sleek_source_view ?(text = "") () =

  let get_sleek_lang () =
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    language_manager#set_search_path ("." :: language_manager#search_path);
    let res = match language_manager#guess_language ~content_type:lang_mime_type () with
      | None -> failwith ("no language for " ^ lang_mime_type)
      | Some lang -> lang
    in res
  in

  object (self)
    inherit source_view ~text () as super
    
    initializer
      super#source_buffer#set_language (Some (get_sleek_lang ()));
      super#source_buffer#set_highlight_syntax true;

    (** highlight checkentail command
       by applying checkentail tag on that part of source code *)
    method hl_entailment (e: entailment): unit =
      super#hl_segment ~clear_previous_highlight:true ~scroll:true e.pos

    (** highlight all checkentail commands *)
    method hl_all_entailement () : unit =
      let src = self#source_buffer#get_text () in
      let e_list = parse_entailment_list src in
      List.iter (fun e -> super#hl_segment e.pos) e_list

  end


(**
   Hip source view
 *)
class hip_source_view ?(text = "") () =

  let get_hip_lang () =
    (* TODO: syntax definition for hip *)
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    language_manager#set_search_path ("." :: language_manager#search_path);
    let res = match language_manager#guess_language ~content_type:lang_mime_type () with
      | None -> failwith ("no language for " ^ lang_mime_type)
      | Some lang -> lang
    in res
  in

  object (self)
    inherit source_view ~text () as super
    
    initializer
      super#source_buffer#set_language (Some (get_hip_lang ()));
      super#source_buffer#set_highlight_syntax true;

    method hl_proc (p: procedure): unit =
      super#hl_segment ~clear_previous_highlight:true ~scroll:true p.pos

  end

