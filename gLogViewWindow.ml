module SU = GUtil.SourceUtil

class log_view_window log =
  let tag_results = "results" in
  let tag_current = "current" in
  let win = GWindow.window
    ~height:600 ~width:850
    ~title:"Debug Log"
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    val log_view = GText.view ~editable:false ~wrap_mode:`WORD ()
    val search_field = GEdit.entry ()
    val status_lbl = GMisc.label ()
    val mutable current_index = 0
    val mutable search_results = []
    val mutable current_pos = None

    initializer
      status_lbl#set_use_markup true;
      let h_separator = GMisc.separator `HORIZONTAL () in
      let v_separator = GMisc.separator `VERTICAL () in
      let log_panel = GUtil.create_scrolled_win log_view in
      log_view#buffer#set_text log;
      let action_panel = GPack.hbox ~spacing:10 ~border_width:10 () in
      let search_lbl = GMisc.label ~text:"Find:" () in
      let next_btn = GButton.button ~label:"Next" () in
      let prev_btn = GButton.button ~label:"Previous" () in
      let buttons = GPack.button_box `HORIZONTAL () in
      buttons#pack next_btn#coerce;
      buttons#pack prev_btn#coerce;
      let close_btn = GButton.button ~label:"  Close  " () in
      action_panel#pack search_lbl#coerce;
      action_panel#pack ~expand:true search_field#coerce;
      action_panel#pack status_lbl#coerce;
      action_panel#pack buttons#coerce;
      action_panel#pack ~padding:5 v_separator#coerce;
      action_panel#pack close_btn#coerce;
      ignore (close_btn#connect#clicked ~callback:(fun _ -> self#destroy ()));
      let vbox = GPack.vbox ~packing:self#add () in
      vbox#pack ~expand:true log_panel#coerce;
      vbox#pack action_panel#coerce;
      ignore (log_view#buffer#create_tag ~name:tag_results [`BACKGROUND "yellow"]);
      ignore (log_view#buffer#create_tag ~name:tag_current [`BACKGROUND "orange"]);
      (* set event handlers *)
      ignore (search_field#connect#changed
        ~callback:self#search_field_changed_handler);
      ignore (search_field#event#connect#key_press
        ~callback:self#key_press_handler);
      ignore (next_btn#connect#clicked ~callback:self#find_next);
      ignore (prev_btn#connect#clicked ~callback:self#find_previous);

    method search_field_changed_handler () =
      let trimmed = Util.trim_str search_field#text in
      if String.length trimmed > 0 then
        let found = self#find_all (search_field#text) in
        if found then
          self#find_next ()
        else self#set_status "<span background='red'>0 of 0</span>"
      else
        (self#clear_highlight (); self#set_status "")

    method key_press_handler key =
      let enter_key = 36 in
      let num_enter_key = 104 in
      let keycode = GdkEvent.Key.hardware_keycode key in
      if keycode = enter_key or keycode = num_enter_key then 
        self#find_next ();
      false

    method pos2iters (pos: SU.substring_pos) =
      let start = log_view#buffer#get_iter_at_char pos.SU.start in
      let stop = log_view#buffer#get_iter_at_char pos.SU.stop in
      start, stop

    method apply_tag (tag: string) (pos: SU.substring_pos) =
      let start, stop = self#pos2iters pos in
      log_view#buffer#apply_tag_by_name tag start stop

    method remove_tag (tag: string) (pos: SU.substring_pos) =
      let start, stop = self#pos2iters pos in
      log_view#buffer#remove_tag_by_name tag start stop

    method find_all (sub: string) =
      (* clear current highlight *)
      self#clear_highlight ();
      (* search *)
      let doc = log_view#buffer#get_text () in
      let res = SU.search doc sub in
      (* update current state and highlight all results *)
      search_results <- res;
      current_index <- -1;
      current_pos <- None;
      List.iter (self#apply_tag tag_results) res;
      let found = (List.length res) > 0 in
      found

    method find_next () =
      if (List.length search_results) > 0 then
        let next_idx = (current_index + 1) mod (List.length search_results) in
        self#goto_search_result next_idx

    method find_previous () =
      if (List.length search_results) > 0 then
        let length = List.length search_results in
        let prev_idx = (current_index - 1) mod length in
        let prev_idx = if prev_idx < 0 then length-1 else prev_idx in
        self#goto_search_result prev_idx

    method goto_search_result idx =
      (* unhighlight current pos *)
      let _ = match current_pos with
        | Some pos -> 
            self#remove_tag tag_current pos;
            self#apply_tag tag_results pos
        | None -> ()
      in
      (* get next pos and it's iter *)
      let pos = List.nth search_results idx in
      let iter = log_view#buffer#get_iter_at_char pos.SU.start in
      (* scroll to and highlight it *)
      ignore (log_view#scroll_to_iter iter);
      self#apply_tag tag_current pos;
      (* update current state *)
      current_index <- idx;
      current_pos <- Some pos;
      self#set_status (Printf.sprintf "%d of %d" (idx+1)  (List.length search_results))

    method clear_highlight () =
      let start = log_view#buffer#get_iter `START in
      let stop = log_view#buffer#get_iter `END in
      log_view#buffer#remove_tag_by_name tag_current start stop;
      log_view#buffer#remove_tag_by_name tag_results start stop

    method set_status (msg: string) =
      status_lbl#set_label msg

  end

