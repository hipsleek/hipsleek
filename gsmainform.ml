(**
   GUI frontend for Sleek
 *)

open Resource
open GSourceViewX
open GUtil
open GUtilSleek

module HDL = MainformHdl
module SU = SourceUtil
module FU = FileUtil


let create_context_view () =
  let view = GText.view
    ~editable:false
    ~wrap_mode:`WORD
    () in
  view

let create_proof_view () =
  let view = GText.view
    ~editable:false
    ~wrap_mode:`WORD
    () in
  view

class mainwindow () =
(*resource.ml*)
  let ui_info = "<ui>" ^ !string_menu_bar ^ !string_tool_bar ^ "</ui>"
  in
  let win = GWindow.window
    ~height:750 ~width:1000
    ~title:!strinng_title
    ~allow_shrink:true
    () in
  object (self)
    inherit GWindow.window win#as_window as super

    (* gui components *)
    val slk_view = new sleek_source_view ()
   (* val entailment_list = new entailment_list ()*)
    val proof_view = create_proof_view ()
    val context_view = create_context_view ()
    (* data *)
    val mutable original_digest = ""
    val mutable debug_log_window = None
    val mutable prover_log_window = None

    initializer
      (* initialize components *)
      let proof_panel =
        let list_scrolled = create_scrolled_win proof_view in
        let buttons = GPack.button_box
          `HORIZONTAL ~layout:`START
          ~border_width:10
          () in
        let check_btn = GButton.button
          ~label:"Save proof"
          ~packing:buttons#add
          () in
        ignore (check_btn#connect#clicked ~callback:(self#save_current_proof(*check_selected_entailment*) ~force:true));
        let show_debug_log_btn = GButton.button
          ~label:"Debug Log"
          ~packing:buttons#add
          () in
        ignore (show_debug_log_btn#connect#clicked ~callback:self#show_debug_log);
        let show_prover_log_btn = GButton.button
          ~label:"Prover Log"
          ~packing:buttons#add
          () in
        ignore (show_prover_log_btn#connect#clicked ~callback:self#show_prover_log);
        let vbox = GPack.vbox () in
        vbox#pack ~expand:true list_scrolled#coerce;
        vbox#pack ~expand:false buttons#coerce;
        vbox
      in
      let context_panel =
        let label = GMisc.label
          ~text:"Context:"
          ~xalign:0.0 ~yalign:0.0
          ~xpad:5 ~ypad:5
          () in
        let context_scrolled = create_scrolled_win context_view in
        let vbox = GPack.vbox () in
        vbox#pack ~expand:false label#coerce;
        vbox#pack ~expand:true context_scrolled#coerce;
         let vpaned = GPack.paned `VERTICAL () in
        vpaned#set_position 380;
        vpaned#pack1 vbox#coerce;
        vpaned#pack2 ~resize:true ~shrink:true proof_panel#coerce;
        vpaned
      in
      let main_panel =
        let hpaned = GPack.paned `HORIZONTAL () in
        hpaned#set_position 550;
        hpaned#pack1 ~resize:true ~shrink:true slk_view#coerce;
        hpaned#pack2 context_panel#coerce;
        hpaned
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
      ignore (slk_view#source_buffer#connect#end_user_action
        ~callback:self#source_changed_handler);
      ignore (slk_view#connect#undo ~callback:self#source_changed_handler);
      ignore (slk_view#connect#redo ~callback:self#source_changed_handler);
(*
      ignore (slk_view#event#connect#focus_out
        ~callback:(fun _ -> self#update_entailment_list (); false));
      ignore (entailment_list#selection#connect#changed
        ~callback:self#check_selected_entailment);
      entailment_list#set_checkall_handler self#run_all_handler;
*)

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
        a "New" ~stock:`NEW ~tooltip:"New file"
          ~callback:(fun _ -> ignore (self#new_file_handler ()));
        a "Open" ~stock:`OPEN ~tooltip:"Open file"
          ~callback:(fun _ -> ignore (self#open_handler ()));
        a "Save" ~stock:`SAVE ~tooltip:"Save"
          ~callback:(fun _ -> ignore (self#save_handler ()));
        a "Quit" ~stock:`QUIT ~tooltip:"Quit"
          ~callback:(fun _ -> ignore (self#quit ()));
        a "About" ~label:"_About" ~tooltip:"About HIP/Sleek"
          ~callback:(fun _ -> ignore (self#show_about_dialog ()));
        a "Execute" ~stock:`EXECUTE ~tooltip:"Check all entailments"
          ~callback:(fun _ -> self#exec_handler ());
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
        ta "EPS" ~label:"Specialization"
          ~callback:(fun act -> Globals.allow_pred_spec := act#get_active);
        radio ~init_value:0 ~callback:self#set_theorem_prover [
          ra "Omega" 0 ~label:"_Omega";
          ra "Mona" 1 ~label:"_Mona";
          ra "Redlog" 2 ~label:"_Redlog";
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
        GFile.filter ~name:"Sleek files" ~patterns:["*.slk"] ()
      in
      let dialog = GWindow.file_chooser_dialog
        ~action ~title
        ~parent:self 
        () in
      let current_name = slk_view#get_current_file_name() in
      let dir = if (current_name = !string_default_file_name) || (current_name = "")
          then Filename.current_dir_name
          else Filename.dirname current_name
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
      let current_name = slk_view#get_current_file_name() in
      let save_msg = if (current_name = !string_default_file_name) || (current_name = "")
          then "Save" else "Save as..."
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

    method source_changed (new_src: string): unit =
      self#update_original_digest ();
(*      entailment_list#update_source new_src;*)
      context_view#buffer#set_text ""

    method private string_of_current_file () =
      let current_file = slk_view#get_current_file_name () in
      match current_file with
      | "" -> !string_default_file_name
      | fname -> fname

    method file_closing_check (): bool =
      if slk_view#source_buffer#modified then
        self#ask_for_saving ()
      else
        true

    method open_file (fname: string): unit =
      let src = slk_view#load_new_file fname in
      self#source_changed src;
      let ctxs, prfs =  slk_view#process_decl_cmd() in
      (self#update_ctx_prf_view ctxs prfs);
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
      let title = prefix ^ fname ^ " - Sleek" in
      self#set_title title;
        
    method get_text () = slk_view#source_buffer#get_text ()

    method update_original_digest () =
      original_digest <- Digest.string (self#get_text ())

    method source_modified =
      let digest = Digest.string (self#get_text ()) in
      original_digest <> digest

    method set_theorem_prover id =
      HDL.set_theorem_prover id

    method save_current_proof ?(force=false) () =
      ()
(*
    method check_selected_entailment ?(force=false) () =
      let entail = entailment_list#get_selected_entailment () in
      match entail with
      | None -> ()
      | Some e -> begin
          source_view#hl_entailment e;
          let current_validity = entailment_list#get_selected_entailment_validity () in
          if current_validity = None || force then begin
            let src = self#get_text () in
            let valid, residue = SH.checkentail src e in
            entailment_list#set_selected_entailment_validity valid;
            residue_view#buffer#set_text residue
          end
        end
*)
    method show_debug_log () =
      let log = Debug.get_debug_log () in
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
      let log = TP.get_prover_log () in
      let title = (TP.get_current_tp_name ()) ^ " Log" in
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

    method show_about_dialog () =
        let dialog = GWindow.about_dialog
          ~name:"HIP/Sleek"
          ~authors:["Wei Ngan Chin"; "Huu Hai Nguyen"; "Cristina David"; "Cristian Gherghina"]
          ~version:"1.0"
          ~website:"http://loris-7.ddns.comp.nus.edu.sg/~project/hip/index.html"
          ~parent:self
          () in
        ignore (dialog#connect#response ~callback:(fun _ -> dialog#destroy ()));
        dialog#show ()

    (*********************
     * Actions handlers
     *********************)

    method private new_file_handler () =
      if self#file_closing_check () then begin
          let src = slk_view#create_new_file() in
          self#update_win_title ();
          slk_view#replace_source src;
          self#source_changed src
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
      self#update_original_digest ();
      self#update_win_title ()

    (* Toolbar's Save button clicked 
     * return true if file is saved successfully
     * return false if user don't select a file to save *)
    method private save_handler () : bool =
      let text = self#get_text () in
      let current_file = slk_view#get_current_file_name () in
      match current_file with
      | "" ->
          begin
              let fname = self#show_file_chooser ~title:"Save As..." `SAVE in
              match fname with
                | None -> false
                | Some fname -> (self#save text fname; true)
          end
      | fname -> (if self#source_modified then self#save text fname; true)

    method private update_ctx_prf_view ctx prf:unit=
      if String.length (ctx^prf)>0 then
        begin
            context_view#buffer#set_text ctx;
            proof_view#buffer#set_text prf;
            ()
        end
      else ()

    (* Toolbar's Run all button clicked or Validity column header clicked *)
    method private exec_handler () =
      let ctxs,prfs=slk_view#exec_current_cmd() in
      (self#update_ctx_prf_view ctxs prfs)
    (*  let src = self#get_text () in
    (*  entailment_list#check_all (fun e -> fst (SH.checkentail src e));*)
      if src == "" then () else
        slk_view#hl_all_cmd ()
      ()
    *)

    (* Source buffer modified *)
    method private source_changed_handler () =
      self#update_win_title ();
      slk_view#clear_highlight ()
(*
    method private update_entailment_list () =
      entailment_list#misc#set_sensitive true;
      let source = self#get_text () in
      let digest = Digest.string source in
      if entailment_list#source_digest <> digest then begin
        entailment_list#update_source (self#get_text ())
      end
*)
    method private quit () =
      if self#file_closing_check () then
        let _ = GMain.quit () in
        false
      else
        true

     method private next_action_handler () =
       let _ = print_endline "next step. not implemented yet" in
       ()

     method private up_action_handler () =
        let _ = print_endline "previous step. not implemented yet" in
       ()

      method private go_forward_action_handler () =
       let _ = print_endline "next command" in

       let ctx,prf=slk_view#exec_current_cmd() in
       let _ =
       if String.length (ctx^prf)>0 then
         begin
             context_view#buffer#set_text ctx;
             proof_view#buffer#set_text prf;
             ()
         end
       else () in
       slk_view#move_to_next_cmd()

     method private go_back_action_handler () =
        let _ = print_endline "previous command" in
        slk_view#back_to_prev_cmd()

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
