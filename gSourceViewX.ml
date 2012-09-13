(**
   Extended source view
 *)

open Globals
open Gen
open GUtil
open GUtilSleek
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
      Debug.ho_2 "hl_segment" pr pr (fun () -> "out") (fun _ _ -> self#hl_segment_x ~clear_previous_highlight
          ~scroll bpos epos) bpos epos

    method hl_error ?(msg = "Error in source document") ?(mark = true) (* (bpos: int) (epos: int) *) pos =
      let bpos = pos.start_line in
      let epos = pos.stop_line in
      if mark then self#create_mark error bpos;
      self#apply_tag error bpos epos;
      self#scroll_to_pos bpos;
      if msg <> "" then
        let msg = Printf.sprintf 
          "<span font_variant='smallcaps' font_weight='bold' color='#fff' bgcolor='#b24c40'>  %s  </span>"
          msg in
        self#set_status msg

    method hl_ee ?(mark = true) (bpos: int) (epos: int) =
      if mark then self#create_mark error bpos;
      self#apply_tag error bpos epos;
      (* self#scroll_to_pos bpos; *)

    method clear_ee_highlight () =
      let start = self#source_buffer#get_iter `START in
      let stop = self#source_buffer#get_iter `END in
      self#source_buffer#remove_tag_by_name error start stop;
      self#source_buffer#remove_source_marks ~category:error ~start ~stop ();

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

    val mutable current_file = new sleek_file_info;
    val mutable is_accessible = false

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
      is_accessible <- false;
      let (cur_line_pos, src) = current_file#load_new_file fname in
      (*replace source*)
      self#replace_source src;
      (*highlight cur_pos*)
      self#highlight_line cur_line_pos;
      is_accessible <- true;
      (src)

    method process_decl_cmd():(string*string)=
      (*exec all decl cmds*)
      let ctxs, prfs = current_file#process_cmds (current_file#get_decl_cmds()) in
      (ctxs, prfs)

    method create_new_file ():string=
      let (cur_pos, src) = current_file#create_new_file () in
      (*highlight cur_pos*)

      src

    method private is_valid_document (): bool= is_accessible
   
    method replace_source (new_src: string): unit =
      self#source_buffer#begin_not_undoable_action ();
      self#source_buffer#set_text new_src;
      self#source_buffer#set_modified false;
      self#source_buffer#end_not_undoable_action ();

    method exec_current_cmd():(string*string)=
    (*process current cmd to the end*)
    (*get context string * proof string*)
    let rs, prf = current_file#process_remain_current_cmd() in
           (rs,prf)

   method move_to_next_cmd ():unit=
   (*res = new pos, new cmd*)
     if self#is_valid_document () then
       begin
           (*move to next cmd*)
           let cur_line_pos= current_file#move_to_next_cmd() in
           self#highlight_line cur_line_pos
       end
     else ()

  method back_to_prev_cmd ():unit=
   (*res = new pos, new cmd*)
   if self#is_valid_document () then
     begin
         let cur_line_pos= current_file#back_to_prev_cmd() in
         self#highlight_line cur_line_pos;
         ()
     end
   else ()

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

    val mutable m_lines_pos = ([]: (int*int) list) (*mapping from line number -> begin char, end char*)

    initializer
      super#source_buffer#set_language (Some (get_hip_lang ()));
      super#source_buffer#set_highlight_syntax true;
      m_lines_pos <- [];
    (* method hl_proc (p: procedure): unit = *)
    (*   super#hl_segment ~clear_previous_highlight:true ~scroll:true 2 10 *)

    method set_lines_pos src=
      m_lines_pos <- (SourceUtil.get_lines_positions src);

    method highlight_ee_x ?(clear_previous_highlight = false) elocs=
      let hl_one_loc eloc=
        let rel_eloc_b,rel_eloc_e  = SourceUtil.get_line_pos eloc m_lines_pos in
        let _ = super#hl_ee rel_eloc_b rel_eloc_e in ()
      in
      if clear_previous_highlight then super#clear_ee_highlight ();
      List.iter hl_one_loc elocs

    method highlight_ee ?(clear_previous_highlight = true) elocs=
      let pr1 = pr_list string_of_int in
      let pr2 = fun _ -> "out" in
      Debug.ho_1 "highlight_ee" pr1 pr2 (fun _ -> self#highlight_ee_x ~clear_previous_highlight elocs) elocs

    method scroll_to_proc (p: procedure): unit=
      let b,e = SourceUtil.get_line_pos p.pos.start_line m_lines_pos in
      super#hl_segment ~clear_previous_highlight:true ~scroll:true b e
  end

