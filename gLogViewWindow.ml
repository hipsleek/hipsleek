module SU = GUtil.SourceUtil

class log_view_window log =
  let search_result_tag = "search_result" in
  let enter_keycode = 36 in
  let num_enter_keycode = 104 in
  let win = GWindow.window
    ~height:500 ~width:700
    ~title:"Debug Log"
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    val log_view = GText.view ~editable:false ~wrap_mode:`WORD ()
    val search_field = GEdit.entry ()
    val statusbar = GMisc.statusbar ()
    val mutable search_result_index = 0
    val mutable search_results = []
    val mutable search_field_changed = false

    initializer
      let h_separator = GMisc.separator `HORIZONTAL () in
      let v_separator = GMisc.separator `VERTICAL () in
      let log_panel = GUtil.create_scrolled_win log_view in
      log_view#buffer#set_text log;
      let action_panel = GPack.hbox ~spacing:10 ~border_width:10 () in
      let search_lbl = GMisc.label ~text:"Search:" () in
      let next_btn = GButton.button ~label:"Next" () in
      let prev_btn = GButton.button ~label:"Previous" () in
      let buttons = GPack.button_box `HORIZONTAL () in
      buttons#pack next_btn#coerce;
      buttons#pack prev_btn#coerce;
      let close_btn = GButton.button ~label:"  Close  " () in
      action_panel#pack search_lbl#coerce;
      action_panel#pack ~expand:true search_field#coerce;
      action_panel#pack buttons#coerce;
      action_panel#pack ~padding:5 v_separator#coerce;
      action_panel#pack close_btn#coerce;
      ignore (close_btn#connect#clicked ~callback:(fun _ -> self#destroy ()));
      let vbox = GPack.vbox ~packing:self#add () in
      vbox#pack ~expand:true log_panel#coerce;
      vbox#pack action_panel#coerce;
      vbox#pack statusbar#coerce;
      (* set event handlers *)
      ignore (log_view#buffer#create_tag ~name:search_result_tag [`BACKGROUND "yellow"]);
      ignore (next_btn#connect#clicked ~callback:self#find_next);
      ignore (prev_btn#connect#clicked ~callback:self#find_previous);
      ignore (search_field#connect#changed 
        ~callback:(fun _ -> search_field_changed <- true));
      ignore (search_field#event#connect#key_press
        ~callback:self#key_press_handler);

    method hl_substring (pos: SU.substring_pos) =
      let start = log_view#buffer#get_iter_at_char pos.SU.start in
      let stop = log_view#buffer#get_iter_at_char pos.SU.stop in
      log_view#buffer#apply_tag_by_name search_result_tag start stop

    method find_all (substring: string) =
      self#clear_highlight ();
      let doc = log_view#buffer#get_text () in
      let res = SU.search doc substring in
      let found = List.length res > 0 in
      let msg =
        if not found then Printf.sprintf "\"%s\" not found!" substring
        else ""
      in
      self#set_status msg;
      search_results <- res;
      search_result_index <- -1;
      search_field_changed <- false;
      List.iter self#hl_substring res;
      found

    method find_next () =
      if search_field#text_length > 0 then begin
        let found = 
          if search_field_changed then
            self#find_all (search_field#text)
          else
            (List.length search_results) > 0
        in
        if found then (
          let next_idx = (search_result_index + 1) mod (List.length search_results) in
          self#goto_search_result next_idx
        )
      end

    method find_previous () =
      if search_field#text_length > 0 then begin
        let found = 
          if search_field_changed then
            self#find_all (search_field#text)
          else
            (List.length search_results) > 0
        in
        if found then (
          let next_idx = (search_result_index + 1) mod (List.length search_results) in
          self#goto_search_result next_idx
        )
      end

    method goto_search_result idx =
      let pos = List.nth search_results idx in
      let iter = log_view#buffer#get_iter_at_char pos.SU.start in
      ignore (log_view#scroll_to_iter iter);
      search_result_index <- idx

    (* clear current highlight
     * by removing checkentail tag in current source code *)
    method clear_highlight () =
      let start = log_view#buffer#get_iter `START in
      let stop = log_view#buffer#get_iter `END in
      log_view#buffer#remove_tag_by_name search_result_tag start stop

    method key_press_handler key =
      let keycode = GdkEvent.Key.hardware_keycode key in
      let res = 
        if keycode = enter_keycode or keycode = num_enter_keycode then
          (self#find_next (); true)
        else false
      in res

    method set_status (msg: string) =
      let context = statusbar#new_context ~name:"context" in
      ignore (context#push msg)

  end

