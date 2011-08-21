(**
   Extended source view
 *)

open Globals
open GUtil
open GUtil_sleek
open SourceUtil

class source_view ?(text = "") () =

  let error = "error" in
  let highlight = "highlight" in
  let font_name = "Monospace 11" in
  let color_red = GDraw.color (`RGB (0xee*257, 0xd3*257, 0xd0*257)) in
  let color_highlight_bg = GDraw.color (`RGB (0xd5*257, 0xe5*257, 0xe3*257)) in

  object (self)
    val delegate = GSourceView2.source_view ()
    val panel = GPack.vbox ()
    val status_lbl = GMisc.label ~show:false ~ypad:2 ()
    
    initializer
      status_lbl#set_use_markup true;
      delegate#set_show_line_numbers true;
      delegate#set_highlight_current_line true;
      delegate#set_auto_indent true;
      delegate#set_tab_width 4;
      (*elegate#set_accepts_tab true;*)
      delegate#set_insert_spaces_instead_of_tabs true;
      delegate#misc#modify_font_by_name font_name;
      delegate#set_show_line_marks true;
      let buffer = delegate#source_buffer in
      buffer#set_text text;
      panel#pack ~expand:true (create_scrolled_win delegate)#coerce;
      panel#pack status_lbl#coerce;
      ignore (buffer#create_tag ~name:highlight []);
      ignore (buffer#create_tag ~name:error [`BACKGROUND_GDK color_red]);
      delegate#set_mark_category_background ~category:highlight (Some color_highlight_bg);
      let pixbuf =  delegate#misc#render_icon ~size:`DIALOG `GO_FORWARD in
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

    method private create_mark (category: string) (bpos: int)=
      let start = self#source_buffer#get_iter_at_char bpos in
      ignore (self#source_buffer#create_source_mark ~category start)

    method private apply_tag (tag: string) (bpos: int) (epos: int) =
      let start = self#source_buffer#get_iter_at_char bpos in
      let stop = self#source_buffer#get_iter_at_char  epos in
      self#source_buffer#apply_tag_by_name tag start stop

    (** highlight part of the source and scroll to it *)
    method hl_segment_x ?(clear_previous_highlight = false) ?(scroll = false) (bpos: int) (epos: int) =
      if clear_previous_highlight then self#clear_highlight ();
      self#create_mark highlight bpos;
      self#apply_tag highlight bpos epos;
      if scroll then self#scroll_to_pos bpos

    method hl_segment ?(clear_previous_highlight = false) ?(scroll = false) (bpos: int) (epos: int) =
      let pr = string_of_int in
      Gen.Debug.no_2 "hl_segment " pr pr (fun () -> "out") (fun _ _ -> self#hl_segment_x ~clear_previous_highlight
          ~scroll bpos epos) bpos epos

    method hl_error ?(msg = "Error in source document") ?(mark = true) (bpos: int) (epos: int) =
      if mark then self#create_mark error bpos;
      self#apply_tag error bpos epos;
      self#scroll_to_pos bpos;
      if msg <> "" then
        let msg = Printf.sprintf 
          "<span font_variant='smallcaps' font_weight='bold' color='#fff' bgcolor='#b24c40'>  %s  </span>"
          msg in
        self#set_status msg

    (** clear current highlight
       by removing checkentail tag in current source code *)
    method clear_highlight () =
      let start = self#source_buffer#get_iter `START in
      let stop = self#source_buffer#get_iter `END in
      self#source_buffer#remove_tag_by_name highlight start stop;
      self#source_buffer#remove_tag_by_name error start stop;
      self#source_buffer#remove_source_marks ~category:error ~start ~stop ();
      self#source_buffer#remove_source_marks ~category:highlight ~start ~stop ();

    (** scroll the view window to given position *)
    method scroll_to_pos (bpos: int) =
      let iter = self#source_buffer#get_iter_at_char bpos in
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

    val current_file = new sleek_file_info

    initializer
      super#source_buffer#set_language (Some (get_sleek_lang ()));
      super#source_buffer#set_highlight_syntax true;

      (** highlight a line
       by applying checkentail tag on that part of source code *)
    method highlight_line (line_num: int): unit =
      let (b, e) = SourceUtil.get_line_pos line_num current_file#get_lines_map in
      (*let _ = print_endline ("b: "^(string_of_int b)) in*)
      super#hl_segment ~clear_previous_highlight:true ~scroll:true b e

     (** highlight cmd
       by applying checkentail tag on that part of source code *)
    method highlight_cmd (cmd: cmd_info): unit =
      let m = current_file#get_lines_map in
      let pos = cmd#get_pos in
      let (b1, _) = SourceUtil.get_line_pos pos.start_pos.Lexing.pos_lnum m in
      let (_,e2) = SourceUtil.get_line_pos pos.end_pos.Lexing.pos_lnum m in
      super#hl_segment ~clear_previous_highlight:true ~scroll:true b1 e2

(*
    (** highlight all commands *)
    method hl_all_cmd () : unit =
      List.iter self#hl_cmd current_file
*)
    method get_current_file_name():string=
    current_file#get_file_name

    (*result src of file*)
    method load_new_file (fname:string):string=
      let (cur_line_pos, src) = current_file#load_new_file fname in
      (*replace source*)
      self#replace_source src;
      (*highlight cur_pos*)
      self#highlight_line cur_line_pos;
      src

    method create_new_file ():string=
      let (cur_pos, src) = current_file#create_new_file () in
      (*highlight cur_pos*)

      src

    method replace_source (new_src: string): unit =
      self#source_buffer#begin_not_undoable_action ();
      self#source_buffer#set_text new_src;
      self#source_buffer#set_modified false;
      self#source_buffer#end_not_undoable_action ();

   method move_to_next_cmd ():unit=
   (*res = new pos, new cmd*)
     let cur_line_pos= current_file#move_to_next_cmd() in
     self#highlight_line cur_line_pos;
     ()

  method back_to_prev_cmd ():unit=
   (*res = new pos, new cmd*)
    let cur_line_pos= current_file#back_to_prev_cmd() in
     self#highlight_line cur_line_pos;
    ()

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
      super#hl_segment ~clear_previous_highlight:true ~scroll:true 2 10

  end

