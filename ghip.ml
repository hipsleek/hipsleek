#include "xdebug.cppo"
open VarGen
(**
   GUI frontend for HIP
*)

open Globals
open GProcList
open GSourceViewX
open GUtil
open SourceUtil

module FU = FileUtil
module HH = HipHelper
module TP = Tpdispatcher

class mainwindow () =
  let ui_info =
    "<ui>\
     <menubar name='MenuBar'>\
     <menu action='FileMenu'>\
     <menuitem action='New'/>\
     <menuitem action='Open'/>\
     <menuitem action='Save'/>\
     <separator/>\
     <menuitem action='Quit'/>\
     </menu>\n
      <menu action='PreferencesMenu'>\
     <menu action='TheoremProverMenu'>\
     <menuitem action='Omega'/>\
     <menuitem action='Mona'/>\
     <menuitem action='Cvc4'/>\
     <menuitem action='Redlog'/>\
     <menuitem action='Coq'/>\
     </menu>\
     <menuitem action='eps'/>\
     <menuitem action='eap'/>\
     <menuitem action='esn'/>\
     <menuitem action='esi'/>\
     <menuitem action='efp'/>\
     <menuitem action='cache'/>\
     <menuitem action='increm'/>\
     </menu>\
     <menu action='HelpMenu'>\
     <menuitem action='About'/>\
     </menu>\
     </menubar>\
     <toolbar name='ToolBar'>\
     <toolitem action='New'/>\
     <toolitem action='Open'/>\
     <toolitem action='Save'/>\
     <separator/>\
     <toolitem action='Execute'/>\
     </toolbar>\
     </ui>"
  in
  let win = GWindow.window
      ~height:750 ~width:1000
      ~title:"Unsaved Document - gHip" 
      ~allow_shrink:true
      () in
  object (self)
    inherit GWindow.window win#as_window as super

    (* gui components *)
    val source_view = new hip_source_view ()
    val proc_list = new procedure_list ()
    (* data *)
    val mutable current_file = None
    val mutable original_digest = Digest.string ""
    val mutable args = HH.default_args
    val mutable debug_log_window = None
    val mutable prover_log_window = None
    val mutable console_log_window = None

    val check_btn = GButton.button ~label:"Check Procedure" ()

    initializer
      (* initialize components *)
      check_btn#misc#set_sensitive false;
      ignore (check_btn#connect#clicked ~callback:(self#check_selected_proc ~force:true));
      let proc_panel =
        let list_scrolled = create_scrolled_win proc_list in
        let buttons = GPack.button_box 
            `HORIZONTAL ~layout:`END
            ~child_height:35 ~border_width:10
            () in
        buttons#pack check_btn#coerce;
        let show_console_log_btn = GButton.button
            ~label:"Show Console Output"
            ~packing:buttons#add
            () in
        ignore (show_console_log_btn#connect#clicked ~callback:self#show_console_log);
        let show_debug_log_btn = GButton.button
            ~label:"Show Debug Log"
            ~packing:buttons#add
            () in
        ignore (show_debug_log_btn#connect#clicked ~callback:self#show_debug_log);
        let show_prover_log_btn = GButton.button
            ~label:"Show Prover Log"
            ~packing:buttons#add
            () in
        ignore (show_prover_log_btn#connect#clicked ~callback:self#show_prover_log);
        let vbox = GPack.vbox () in
        vbox#pack ~expand:true list_scrolled#coerce;
        vbox#pack ~expand:false buttons#coerce;
        vbox
      in
      let main_panel =
        let vpaned = GPack.paned `VERTICAL () in
        vpaned#set_position 450;
        vpaned#pack1 ~resize:true ~shrink:true source_view#coerce;
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
      ignore (source_view#source_buffer#connect#end_user_action
                ~callback:self#source_changed_handler);
      ignore (source_view#connect#undo ~callback:self#source_changed_handler);
      ignore (source_view#connect#redo ~callback:self#source_changed_handler);
      ignore (proc_list#selection#connect#changed ~callback:self#check_selected_proc);
      ignore (source_view#event#connect#focus_out
                ~callback:(fun _ -> self#update_proc_list (); false));
      proc_list#set_checkall_handler self#run_all_handler;


      (** Setup UIManager for creating Menubar and Toolbar *)
    method setup_ui_manager () =
      let a = GAction.add_action in
      let radio = GAction.group_radio_actions in
      let ra = GAction.add_radio_action in
      let ta = GAction.add_toggle_action in
      let actions = GAction.action_group ~name:"Actions" () in
      GAction.add_actions actions [ 
        a "FileMenu" ~label:"_File";
        a "PreferencesMenu" ~label:"_Preferences";
        a "TheoremProverMenu" ~label:"_Theorem Prover";
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
          ~callback:(fun _ -> self#run_all_handler ());
        ta "eps" ~label:"Predicate Specialization"
          ~callback:(fun act -> args <- {args with HH.eps = act#get_active});
        ta "eap" ~label:"Aggressive Prunning"
          ~callback:(fun act -> args <- {args with HH.eap = act#get_active});
        ta "esn" ~label:"Simplifier in Fast Imply"
          ~callback:(fun act -> args <- {args with HH.esn = act#get_active});
        ta "esi" ~label:"Strong Predicate Invariant"
          ~callback:(fun act -> args <- {args with HH.esi = act#get_active});
        ta "efp" ~label:"Fast Imply Only for Prunning"
          ~callback:(fun act -> args <- {args with HH.efp = act#get_active});
        ta "cache" ~label:"Cached Checking" ~active:true
          ~callback:(fun act -> args <- {args with HH.cache = act#get_active});
        ta "increm" ~label:"Incremental Proving"
          ~callback:(fun act -> args <- {args with HH.increm = act#get_active});
        radio ~init_value:0 ~callback:self#set_theorem_prover [
          ra "Omega" 0 ~label:"_Omega";
          ra "Mona" 1 ~label:"_Mona";
          ra "Cvc4" 2 ~label:"_Cvc4";
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
      let dir = match current_file with
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
      let save_msg = match current_file with
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

    method replace_source (new_src: string): unit =
      source_view#clear_status ();
      source_view#source_buffer#begin_not_undoable_action ();
      source_view#source_buffer#set_text new_src;
      source_view#source_buffer#set_modified false;
      source_view#source_buffer#end_not_undoable_action ();
      self#update_original_digest ();
      try
        proc_list#update_source (self#get_text ())
      with Syntax_error (msg, pos) ->
        proc_list#misc#set_sensitive false;
        source_view#hl_error ~msg pos

    method private string_of_current_file () =
      match current_file with
      | Some fname -> fname
      | None -> "Unsaved Document"

    method file_closing_check (): bool =
      if self#source_modified then
        self#ask_for_saving ()
      else
        true

    method open_file (fname: string): unit =
      log ("Opening " ^ fname);
      current_file <- (Some fname);
      self#replace_source (FU.read_from_file fname);
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

    method get_text () = source_view#source_buffer#get_text ()

    method update_original_digest () =
      original_digest <- Digest.string (self#get_text ())

    method source_modified =
      let digest = Digest.string (self#get_text ()) in
      original_digest <> digest

    method set_theorem_prover id =
      let provers = [TP.OmegaCalc; TP.Mona; TP.Cvc4; TP.Redlog; TP.Coq] in
      let tp = List.nth provers id in
      args <- {args with HH.tp = tp};
      let tp_name = TP.name_of_tp tp in
      log (Printf.sprintf "Now using %s as backend prover." tp_name)

    method check_selected_proc ?(force = false) () =
      let proc = proc_list#get_selected_procedure () in
      match proc with
      | None -> check_btn#misc#set_sensitive false; ()
      | Some p ->
        check_btn#misc#set_sensitive true;
        source_view#hl_proc p;
        source_view#clear_status ();
        let current_validity = proc_list#get_selected_procedure_validity () in
        (*if source_view#source_buffer#modified || current_validity = None then*)
        if current_validity = None || force then begin
          log ("Checking procedure " ^ p.name);
          let src = self#get_text () in
          let valid = HH.check_proc_external ~args src p in
          proc_list#set_selected_procedure_validity valid;
          let err_pos = HH.get_error_positions () in
          match err_pos with
          | [] -> ()
          | pos::_ -> source_view#hl_error 
                        (* highlight only the first failure's location *)
                        ~msg:"Not all branches are successful!"
                        pos
                        (*if err_pos <> [] then source_view#clear_highlight ();*)
                        (*List.iter (fun pos -> source_view#hl_error ~msg:"" ~mark:false pos) err_pos*)
        end

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

    method private newfile_handler () =
      if self#file_closing_check () then begin
        log "New source file.";
        current_file <- None;
        self#update_win_title ();
        self#replace_source ""
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
      current_file <- Some fname;
      self#update_original_digest ();
      self#update_win_title ()

    (* Toolbar's Save button clicked 
     * return true if file is saved successfully
     * return false if user don't select a file to save *)
    method private save_handler () : bool =
      let text = self#get_text () in
      match current_file with
      | Some name ->
        if self#source_modified then self#save text name;
        true
      | None ->
        let fname = self#show_file_chooser ~title:"Save As..." `SAVE in
        match fname with
        | None -> false
        | Some fname -> (self#save text fname; true)

    (* Toolbar's Run all button clicked or Validity column header clicked *)
    method private run_all_handler () =
      log "Checking all procedures.";
      let src = self#get_text () in
      proc_list#check_all (HH.check_proc_external ~args src)

    (* Source buffer modified *)
    method private source_changed_handler () =
      self#update_win_title ();
      source_view#clear_status ();
      source_view#clear_highlight ()

    method private update_proc_list () =
      proc_list#misc#set_sensitive true;
      let source = self#get_text () in
      let digest = Digest.string source in
      if proc_list#source_digest <> digest then begin
        try
          proc_list#update_source (self#get_text ());
        with Syntax_error (msg, pos) ->
          (*proc_list#misc#set_sensitive false;*)
          source_view#hl_error ~msg pos
      end

    method private quit () =
      if self#file_closing_check () then begin
        log ("Quit.");
        GMain.quit ();
        false
      end else
        true

  end


(**********************
 * MAIN FUNCTION
 **********************)
let usage_msg = Sys.argv.(0) ^ " [options] <source file>"
let arguments = [
  ("-v", Arg.Set verbose_flag, "Verbose")
]

let _ =
  (*GUtil.initialize ();*)
  Globals.reporter := (fun loc msg ->
      let pos = {
        SourceUtil.start_char = loc.start_pos.Lexing.pos_cnum;
        SourceUtil.stop_char = loc.end_pos.Lexing.pos_cnum;
        SourceUtil.start_line = loc.start_pos.Lexing.pos_lnum;
        SourceUtil.stop_line = loc.end_pos.Lexing.pos_lnum;
      } in
      raise (SourceUtil.Syntax_error ("Syntax error: " ^ msg, pos))
    );
  ignore (GtkMain.Main.init ());
  let win = new mainwindow () in
  Arg.parse arguments win#open_file usage_msg;
  win#show ();
  GMain.Main.main ();
  (*GUtil.finalize ()*)

