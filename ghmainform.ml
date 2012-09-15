(**
  GUI frontend for HIP
 *)

open Globals
open Gen
open GProcList
open GSourceViewX
open GUtil
open Ghcontroller
open SourceUtil

module RE = Resource
module FU = FileUtil
module EV = Geeview
module HH = HipHelper
module TP = Tpdispatcher


let create_word_view () =
  let view = GText.view
    ~editable:false
    ~wrap_mode:`WORD
    () in
  view

class mainwindow () =
  let ui_info = "<ui>" ^ !RE.string_menu_bar ^ !RE.string_tool_bar ^ "</ui>" in
  let win = GWindow.window
    ~height:750 ~width:1000
    ~title:"Unsaved Document - gHip" 
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    (* gui components *)
    val m_src_view = new hip_source_view ()
    val m_proc_list = new procedure_list ()
    val m_proc_ee = new EV.ee_view ()
    val m_proc_emsg = create_word_view ()
    (* data *)
    val mutable m_current_file = None
    val mutable m_iprog = None
    val mutable m_cprog = None
    val mutable original_digest = Digest.string ""
    (* val mutable args = HH.default_args *)
    val mutable debug_log_window = None
    val mutable prover_log_window = None
    val mutable console_log_window = None

    val check_btn = GButton.button ~label:"Check Procedure" ()

    initializer
      (* initialize components *)
      check_btn#misc#set_sensitive false;
      ignore (check_btn#connect#clicked ~callback:(self#verify_selected_proc ~force:true));
      let proc_panel =
        let list_scrolled = create_scrolled_win m_proc_list in
        let ee_scrolled = create_scrolled_win m_proc_ee in
        (* let buttons = GPack.button_box  *)
        (*   `HORIZONTAL ~layout:`END *)
        (*   ~child_height:35 ~border_width:10 *)
        (*   () in *)
        (* buttons#pack check_btn#coerce; *)
        (* let show_console_log_btn = GButton.button *)
        (*   ~label:"Show Console Output" *)
        (*   ~packing:buttons#add *)
        (*   () in *)
        (* ignore (show_console_log_btn#connect#clicked ~callback:self#show_console_log); *)
        (* let show_debug_log_btn = GButton.button *)
        (*   ~label:"Show Debug Log" *)
        (*   ~packing:buttons#add *)
        (*   () in *)
        (* ignore (show_debug_log_btn#connect#clicked ~callback:self#show_debug_log); *)
        (* let show_prover_log_btn = GButton.button *)
        (*   ~label:"Show Prover Log" *)
        (*   ~packing:buttons#add *)
        (*   () in *)
        (* ignore (show_prover_log_btn#connect#clicked ~callback:self#show_prover_log); *)
        (* let vbox = GPack.vbox () in *)
        (* vbox#pack ~expand:true list_scrolled#coerce; *)
        (* vbox#pack ~expand:false buttons#coerce; *)
        (* vbox *)
        let hpaned = GPack.paned `HORIZONTAL () in
        hpaned#pack1 ~resize:true ~shrink:true list_scrolled#coerce;
         let vppaned = GPack.paned `VERTICAL () in
          let emsg_scrolled = create_scrolled_win m_proc_emsg in
          vppaned#pack1 ~resize:true ~shrink:true emsg_scrolled#coerce;
          vppaned#pack2 ~resize:true ~shrink:true ee_scrolled#coerce;
         hpaned#pack2 ~resize:true ~shrink:true vppaned#coerce;
        hpaned
      in
      let main_panel =
        let vpaned = GPack.paned `VERTICAL () in
        vpaned#set_position 450;
        vpaned#pack1 ~resize:true ~shrink:true m_src_view#coerce;
        vpaned#pack2 proc_panel#coerce;
        vpaned
      in
      (* arrange components on main window *)
      let ui = self#setup_ui_manager () in
      let toolbar = ui#get_widget "/ToolBar" in
      let menubar = ui#get_widget "/MenuBar" in
      let vbox = GPack.vbox ~packing:self#add () in
      vbox#pack menubar;
      vbox#pack toolbar;
      vbox#pack ~expand:true ~fill:true main_panel#coerce;

      (* set event handlers *)
      ignore (self#event#connect#delete ~callback:(fun _ -> self#quit ()));
      ignore (m_src_view#source_buffer#connect#end_user_action
        ~callback:self#source_changed_handler);
      ignore (m_src_view#connect#undo ~callback:self#source_changed_handler);
      ignore (m_src_view#connect#redo ~callback:self#source_changed_handler);
      ignore (m_proc_list#selection#connect#changed ~callback:self#verify_selected_proc);
      ignore (m_proc_ee#selection#connect#changed ~callback:self#highlight_ee_selected_proc);
      ignore (m_src_view#event#connect#focus_out
        ~callback:(fun _ -> self#update_proc_list (); false));
      m_proc_list#set_checkall_handler self#verify_all_handler;


    (** Setup UIManager for creating Menubar and Toolbar *)
    method setup_ui_manager () =
      let a = GAction.add_action in
      let radio = GAction.group_radio_actions in
      let ra = GAction.add_radio_action in
      let ta = GAction.add_toggle_action in
      let actions = GAction.action_group ~name:"Actions" () in
      GAction.add_actions actions [ 
        a "FileMenu" ~label:"_File";
        a "OptionsMenu" ~label:"_Options";
        a "ProversMenu" ~label:"_Provers";
        a "HelpMenu" ~label:"_Help";
        a "New" ~stock:`NEW ~tooltip:"Create a new file"
          ~callback:(fun _ -> ignore (self#newfile_handler ()));
        a "Open" ~stock:`OPEN ~tooltip:"Open a file"
          ~callback:(fun _ -> ignore (self#open_handler ()));
        a "Save" ~stock:`SAVE ~tooltip:"Save current file"
          ~callback:(fun _ -> ignore (self#save_handler ()));
        a "Quit" ~stock:`QUIT ~tooltip:"Quit"
          ~callback:(fun _ -> ignore (self#quit ()));
        a "About" ~label:"_About" ~tooltip:"About HIP/Sleek"
          ~callback:(fun _ -> ignore (self#show_about_dialog ()));
        a "Execute" ~stock:`EXECUTE ~tooltip:"Check all procedures"
          ~callback:(fun _ -> self#verify_all_handler ());
         a "NextA" ~stock:`GO_DOWN ~tooltip:"Down"
          ~callback:(fun _ -> self#next_action_handler ());
        a "UpA" ~stock:`GO_UP ~tooltip:"Up"
          ~callback:(fun _ -> self#up_action_handler ());
         a "ForwardA" ~stock:`GO_FORWARD ~tooltip:"Next"
          ~callback:(fun _ -> self#go_forward_action_handler ());
        a "BackA" ~stock:`GO_BACK ~tooltip:"Back"
          ~callback:(fun _ -> self#go_back_action_handler ());
         a "NextToE" ~stock:`GOTO_LAST ~tooltip:"Down to the end"
          ~callback:(fun _ -> self#move_to_last_handler ());
        a "UpToB" ~stock:`GOTO_FIRST ~tooltip:"Up to beginning"
          ~callback:(fun _ -> self#back_to_first_handler ());
        a "JumpTo" ~stock:`JUMP_TO ~tooltip:"Jump to current point"
          ~callback:(fun _ -> self#jump_to_handler ());
        ta "EPS" ~label:"Predicate Specialization"
          ~callback:(fun act -> Globals.allow_pred_spec := act#get_active);
        radio ~init_value:0 ~callback:self#set_theorem_prover [
          ra "Omega" 0 ~label:"_Omega";
          ra "Mona" 1 ~label:"_Mona";
          ra "Cvc3" 2 ~label:"_Cvc3";
          ra "Redlog" 3 ~label:"_Redlog";
          ra "Coq" 4 ~label:"Co_q";
        ];
      ];
      let ui = GAction.ui_manager () in
      ui#insert_action_group actions 0;
      self#add_accel_group ui#get_accel_group;
      ignore (ui#add_ui_from_string ui_info);
      ui


    (** open file chooser dialog with parent window
       return choosen file name 
     *)
    method show_file_chooser ?(title="Select file") action : string option =
      let all_files () =
        GFile.filter ~name:"All files" ~patterns:["*"] ()
      in
      let slk_files () =
        GFile.filter ~name:"Hip source files" ~patterns:["*.ss"] ()
      in
      let dialog = GWindow.file_chooser_dialog
        ~action ~title
        ~parent:self 
        () in
      let dir = match m_current_file with
        | Some name -> Filename.dirname name
        | None -> Filename.current_dir_name
      in
      ignore (dialog#set_current_folder dir);
      dialog#add_button_stock `CANCEL `CANCEL;
      dialog#add_select_button_stock `OPEN `OPEN;
      dialog#add_filter (slk_files ());
      dialog#add_filter (all_files ());
      let res = match dialog#run () with
        | `OPEN -> dialog#filename
        | `DELETE_EVENT | `CANCEL -> None 
      in
      dialog#destroy ();
      res

    (** open an yes/no/cancel dialog which asks user for
       saving of modified document *)
    method ask_for_saving () =
      let fname = Filename.basename (self#string_of_current_file ()) in
      let save_msg = match m_current_file with
        | Some _ -> "Save"
        | None -> "Save as..."
      in
      let icon = GMisc.image 
        ~stock:`DIALOG_WARNING 
        ~icon_size:`DIALOG
        () in
      let response = GToolbox.question_box
        ~title:""
        ~buttons:["Discard"; "Cancel"; save_msg]
        ~icon:icon#coerce
        ~default:3
        ("\nSave changes to file \"" ^ fname ^ "\"\nbefore closing?\n")
        in
      let res = match response with
        | 1 -> true
        | 3 -> self#save_handler ()
        | _ -> false
      in res

    method replace_source (new_src: string) fname: unit =
      m_src_view#clear_status ();
      m_src_view#source_buffer#begin_not_undoable_action ();
      m_src_view#source_buffer#set_text new_src;
      m_src_view#source_buffer#set_modified false;
      m_src_view#source_buffer#end_not_undoable_action ();
      self#update_original_digest ();
      try
        (*get cast and procedure list*)
          let iprog,cprog = HH.get_cprog fname in
          let _ = m_cprog <- cprog in
          let _ = m_iprog <- iprog in
          let _ = m_src_view#set_lines_pos (self#get_text()) in
        (* m_proc_list#update_source (self#get_text ()) *)
          match iprog,cprog with
            | Some iprog, Some cprog ->
                m_proc_list#update_procedures iprog.Iast.prog_proc_decls
                    (Cast.list_of_procs cprog)
              (* (Hashtbl.fold (fun id pd lst -> pd::lst) iprog.Cast.new_proc_decls []) *)
              (self#get_text ())
            | _ ->  m_proc_list#misc#set_sensitive false;
      with Syntax_error (msg, pos) ->
          m_proc_list#misc#set_sensitive false;
          m_src_view#hl_error ~msg pos

    method private string_of_current_file () =
      match m_current_file with
      | Some fname -> fname
      | None -> "Unsaved Document"

    method file_closing_check (): bool =
      if self#source_modified then
        self#ask_for_saving ()
      else
        true

    method open_file (fname: string): unit =
      log ("Opening " ^ fname);
      m_current_file <- (Some fname);
      self#replace_source (FU.read_from_file fname) fname;
      self#update_win_title ()

    method update_win_title () =
      let fname = self#string_of_current_file () in
      let fname = Filename.basename fname in
      let prefix = 
        if self#source_modified then
          "*"
        else
          ""
      in
      let title = prefix ^ fname ^ " - gHip" in
      self#set_title title;

    method get_text () = m_src_view#source_buffer#get_text ()

    method update_original_digest () =
      original_digest <- Digest.string (self#get_text ())

    method source_modified =
      let digest = Digest.string (self#get_text ()) in
      original_digest <> digest

    method set_theorem_prover id =
      let provers = [TP.OmegaCalc; TP.Mona; TP.Cvc3; TP.Redlog; TP.Coq] in
      let tp = List.nth provers id in
      (* args <- {args with HH.tp = tp}; *)
      let tp_name = TP.name_of_tp tp in
      log (Printf.sprintf "Now using %s as backend prover." tp_name)

    (*new_verified_proc*)
    method private update_proc_ee_models cprog new_proc=
     m_cprog= Some (Cast.replace_proc cprog new_proc);
       (*ee*)
      let s,ft =
        if List.length new_proc.Cast.proc_verified > 0 then
          HH.cmb_join_branches (List.tl new_proc.Cast.proc_verified)
              (List.hd new_proc.Cast.proc_verified)
        else ("The procedure does not have body", None)
      in
      (*todo: build ee_model*)
      let ee_model =
        match ft with
          | None ->
              let new_ee_model = (new EV.ee_model ()) in
              (new_ee_model)
          | Some ft ->
              let new_ee_model = new EV.ee_model () in
              let _ = new_ee_model#append_errors_tree ft in
              (new_ee_model)
      in
      (s, ee_model)

    method verify_selected_proc ?(force = false) () =
      let proc = m_proc_list#get_selected_proc_info () in
      match proc with
      | None -> check_btn#misc#set_sensitive false; ()
      | Some p ->
          check_btn#misc#set_sensitive true;
          (* m_src_view#hl_proc p; *)
          m_src_view#scroll_to_proc p;
          m_src_view#clear_status ();
          let _ = m_proc_emsg#buffer#set_text "" in
          let current_validity = m_proc_list#get_selected_procedure_validity () in
          (*if m_src_view#source_buffer#modified || current_validity = None then*)
          if current_validity = None || force then begin
            log ("Checking procedure " ^ p.name);
              let valid = match m_current_file with
                | None -> let src = self#get_text () in
                          let res, _ = HH.check_proc_from_txt src p in res
                | Some _ ->
                    let res,onp= HH.check_proc_from_file m_cprog (* src *) p in
                    let _ =
                      match onp with
                        | Some np ->(
                            match m_cprog with
                              | Some cprog ->
                                  let s,ee_model=self#update_proc_ee_models cprog np in
                                  (*store into model*)
                                  let _ = m_proc_list#set_selected_proc_ee s (Some ee_model) in
                              (*update result*)
                                  let _ = m_proc_emsg#buffer#set_text s in
                              (*ee*)
                                  let _ = m_proc_ee#set_model ee_model in ()
                              | None -> report_error no_pos "ghmainform:check_selected_proc"
                        )
                        | None -> ()
                    in res
              in
            m_proc_list#set_selected_procedure_validity valid;
            let err_pos = HH.get_error_positions () in
            match err_pos with
            | [] -> ()
            | pos::_ -> m_src_view#hl_error 
                (* highlight only the first failure's location *)
                ~msg:"Not all branches are successful!"
                pos
            (*if err_pos <> [] then m_src_view#clear_highlight ();*)
            (*List.iter (fun pos -> m_src_view#hl_error ~msg:"" ~mark:false pos) err_pos*)
          end
          else begin
              (*restore into model*)
              let proc  = m_proc_list#get_selected_proc () in
              (*update result*)
              match proc with
                | Some proc -> let _ = m_proc_emsg#buffer#set_text proc.proc_ee_msg in
                  (*ee*)
                               match proc.proc_ee_model with
                                 | Some ee_mod ->  m_proc_ee#set_model ee_mod
                                 | None -> report_error no_pos "ghmainform:verify_selected_proc"
                | None -> ()
          end

    method highlight_ee_selected_proc ?(force = false) () =
      let _ = print_endline "highlight_ee_selected_proc" in
      let elocs = m_proc_ee#get_selected_elocs () in
      let _ = m_src_view#highlight_ee elocs in
      ()

    method show_debug_log () =
      let log = HH.get_debug_log () in
      let win = match debug_log_window with
        | Some win-> 
            win#set_log log;
            win
        | None ->
            let win = new GLogViewWindow.log_view_window
              ~title:"Development Debug Log" log () in
            debug_log_window <- Some win;
            win
      in
      win#present ()

    method show_prover_log () =
      let log = HH.get_prover_log () in
      let title = "Back-end Prover Log" in
      let win = match prover_log_window with
        | Some win-> 
            win#set_log log;
            win#set_title title;
            win
        | None ->
            let win = new GLogViewWindow.log_view_window ~title log () in
            prover_log_window <- Some win;
            win
      in
      win#present ()

    method show_console_log () =
      let log = HH.get_console_log () in
      let win = match console_log_window with
        | Some win-> 
            win#set_log log;
            win
        | None ->
            let win = new GLogViewWindow.log_view_window
              ~title:"Console Output Log" log () in
            debug_log_window <- Some win;
            win
      in
      win#present ()

    method show_about_dialog () =
        let dialog = GWindow.about_dialog 
          ~name:"HIP/Sleek"
          ~authors:["Wei-Ngan Chin"]
          ~version:"1.0"
          ~website:"http://loris-7.ddns.comp.nus.edu.sg/~project/hip/index.html"
          ~parent:self
          () in
        ignore (dialog#connect#response ~callback:(fun _ -> dialog#destroy ()));
        dialog#show ()

    (*********************
     * Actions handlers 
     *********************)

    method private newfile_handler () =
      if self#file_closing_check () then begin
        log "New source file.";
        m_current_file <- None;
        self#update_win_title ();
        self#replace_source "" ""
      end

    (* Toolbar's Open button clicked *)
    method private open_handler () : bool =
      if self#file_closing_check () then
        let fname = self#show_file_chooser ~title:"Open File" `OPEN in
        match fname with
        | None -> false
        | Some fname -> (self#open_file fname; true)
      else
        true

    method private save text fname =
      log ("Saving source to " ^ fname);
      FU.write_to_file fname text;
      m_current_file <- Some fname;
      self#update_original_digest ();
      self#update_win_title ()

    (* Toolbar's Save button clicked 
     * return true if file is saved successfully
     * return false if user don't select a file to save *)
    method private save_handler () : bool =
      let text = self#get_text () in
      match m_current_file with
      | Some name ->
          if self#source_modified then self#save text name;
          true
      | None ->
          let fname = self#show_file_chooser ~title:"Save As..." `SAVE in
          match fname with
          | None -> false
          | Some fname -> (self#save text fname; true)

    (* Toolbar's Run all button clicked or Validity column header clicked *)
    method private verify_all_handler () =
      log "Checking all procedures.";
      let check_proc =
        match m_current_file with
          | None -> let src = self#get_text () in
                    HH.check_proc_from_txt src
          | Some fn ->
              HH.check_proc_from_file m_cprog
      in
      let helper path iter =
        (*check if path is verified?*)
        let _ =
          let v =  m_proc_list#get_procedure_validity path in
          if v=None then
            let proc =  m_proc_list#get_proc_info_by_path path in
            let res,onp = check_proc proc in
            m_proc_list#set_procedure_validity path res;
            let _ =
              match onp with
                | Some np ->(
                    match m_cprog with
                      | Some cprog ->
                          let s,ee_model=self#update_proc_ee_models cprog np in
                          (*store into model*)
                          let _ =m_proc_list#set_proc_ee_by_path path s (Some ee_model) in
                          (* m_cprog= Some (Cast.replace_proc cprog np); *) ()
                      | None -> report_error no_pos "ghmainform:verify_all_handler"
                )
                | None -> ()
            in ()
          else ()
        in false
      in
      let p_mod_d = m_proc_list#get_model_delegate() in
      p_mod_d#foreach helper

    (* Source buffer modified *)
    method private source_changed_handler () =
      self#update_win_title ();
      m_src_view#clear_status ();
      m_src_view#clear_highlight ()

    method private update_proc_list () =
      m_proc_list#misc#set_sensitive true;
      let source = self#get_text () in
      let _ = m_src_view#set_lines_pos source in
      let digest = Digest.string source in
      if m_proc_list#source_digest <> digest then begin
        try
            let _ = m_iprog <- None in
            let _ = m_cprog <- None in
          m_proc_list#update_procedures_from_txt (self#get_text ());
        with Syntax_error (msg, pos) ->
          (*m_proc_list#misc#set_sensitive false;*)
          m_src_view#hl_error ~msg pos
      end

    method private quit () =
      if self#file_closing_check () then begin
        log ("Quit.");
        GMain.quit ();
        false
      end else
        true

     method private next_action_handler () =
       let _ = print_endline "next step. not implemented yet" in
       ()

     method private up_action_handler () =
        let _ = print_endline "previous step. not implemented yet" in
       ()

      method private go_forward_action_handler () =
       let _ = print_endline "next command" in
       ()

     method private go_back_action_handler () =
        let _ = print_endline "previous command" in
        ()

     method private move_to_last_handler () =
        let _ = print_endline "move to the end. not implemented yet" in
        ()

     method private back_to_first_handler () =
        let _ = print_endline "back to the beginning. not implemented yet" in
        ()

     method private jump_to_handler () =
        let _ = print_endline "jump to current point. not implemented yet" in
       ()


  end
