

(* Compile with 
   ocamlc -o viewer -I ../../src/ lablgtk.cma lablgtksourceview.cma gtkInit.cmo test.ml
   Run with 
   CAML_LD_LIBRARY_PATH=../../src ./viewer
*)

open Printf
open StdLabels
open GdkKeysyms
(*open Cast
open Iast*)
open Globals
open Lexing
open Gtk
open Cast

let lang_mime_type = "text/x-ss"
let lang_file = "ss.lang"
let use_mime_type = false
let font_name = "Monospace 10"
let source_file = "global1.ss"
let core_mine_type = "text/core-ss"
let core_lang_file = "core.lang"

let focused_prepost = ref (0,-1)(*(flag,id)*)
let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
		prerr_endline (sprintf "Parsing...\n");
        let _ = Util.push_time "Parsing" in
		let prog = Iparser.program (Ilexer.tokenizer file_name) input in
		  close_in org_in_chnl;
         let _ = Util.pop_time "Parsing" in
			prog 
    with
		End_of_file -> exit 0	  


let file_dialog ~title ~callback ?filename () =
  let sel =
    GWindow.file_selection ~title ~modal:true ?filename () in
  sel#cancel_button#connect#clicked ~callback:sel#destroy;
  sel#ok_button#connect#clicked ~callback:
    begin fun () ->
      let name = sel#filename in
      sel#destroy ();
      callback name
    end;
  sel#show ()


let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
  while len := input ic buf 0 1024; !len > 0 do
    Buffer.add_substring b buf 0 !len
  done

let xpm_label_box ~file ~text ~packing () =
  if not (Sys.file_exists file) then failwith (file ^ " does not exist");

  (* Create box for image and label and pack *)
  let box = GPack.vbox (*~border_width:2*) ~packing () in

  (* Now on to the image stuff and pack into box *)
  let pixmap = GDraw.pixmap_from_xpm ~file () in
  GMisc.pixmap pixmap ~width:40 ~height:40 ~packing:(box#pack ~padding:3) ();

  (* Create a label for the button and pack into box *)
  GMisc.label ~text ~packing:(box#pack) ()
;;

(*let with_file name ~f =
  let ic = open_in name in
  try f ic; close_in ic with exn -> close_in ic; raise exn*)

let print_lang lang = prerr_endline (sprintf "language: %s" lang#get_name)

let print_lang_dirs languages_manager =
  let i = ref 0 in
  prerr_endline "lang_dirs:";
  List.iter
    (fun dir -> incr i; prerr_endline (sprintf "%d: %s" !i dir))
    languages_manager#lang_files_dirs

let win = GWindow.window ~title:"Automated Verification System_TEST" ()

let status_win = GWindow.window ~title:"Program Status"()

let bhbox = GPack.paned `HORIZONTAL ~border_width:5 ~packing:win#add()


let vbox = GPack.vbox ~packing:bhbox#add1 ()

let core_hbox = GPack.hbox ~packing:bhbox#add2()

let core_scrolled_win = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:core_hbox#add()

let core_control_box1 = GPack.button_box `VERTICAL ~child_width:30 ~width: 35 ~layout:`START ~packing:core_hbox#add()
(*let core_control_box2 = GPack.button_box `VERTICAL ~child_width:1 ~width: 1 ~layout:`START ~packing:core_hbox#add()*)
let core_close_button = GButton.button  ~packing:(core_control_box1#pack ~padding:5) ()
let larrow = GMisc.arrow ~kind:`RIGHT ~shadow:`ETCHED_IN ~packing: core_close_button#add ()

(*Menu*)
let menubar = GMenu.menu_bar ~packing:vbox#pack ()

let button_hbox = GPack.button_box `HORIZONTAL ~spacing:2 ~child_width:35(* ~child_height:50 ~height:50*) ~layout:`START ~packing:(vbox#pack)()
let tooltips = GData.tooltips ();;
let open_file_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;
let save_file_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;

let zoom_in_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;
let zoom_out_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;
let link_core_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;
let previous_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;
let next_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack (*~padding:3*)) ();;
let focus_spec_button = GButton.toggle_button ~relief:`NONE ~packing:(button_hbox#pack) ();;
let show_result_button = GButton.button ~relief:`NONE ~packing:(button_hbox#pack) ();;

let _= xpm_label_box ~file:"icon png files/folder-open-small.png" ~text:"open" ~packing:open_file_button#add ();
tooltips#set_tip open_file_button#coerce ~text:"open a file";
xpm_label_box ~file:"icon png files/document-save-as-small.png" ~text:"save" ~packing:save_file_button#add ();
tooltips#set_tip save_file_button#coerce ~text:"save current file";
xpm_label_box ~file:"icon png files/go-next-small.png" ~text:"core" ~packing:link_core_button#add ();
tooltips#set_tip link_core_button#coerce ~text:"highlight the relevant procedure in core according to current cursor position";
xpm_label_box ~file:"icon png files/zoom-in-small.png" ~text:"zoom in" ~packing:zoom_in_button#add ();
tooltips#set_tip zoom_in_button#coerce ~text:"move to a smaller sub-expression inclusive of this position";
xpm_label_box ~file:"icon png files/zoom-out-small.png" ~text:"zoom out" ~packing:zoom_out_button#add ();
tooltips#set_tip zoom_out_button#coerce ~text:"move to a bigger sub-expression inclusive of this position";
xpm_label_box ~file:"icon png files/arrow-right-small.png" ~text:"step down" ~packing:next_button#add ();
tooltips#set_tip next_button#coerce ~text:"move to the next sub-expression";
xpm_label_box ~file:"icon png files/arrow-left-small.png" ~text:"step up" ~packing:previous_button#add ();
tooltips#set_tip previous_button#coerce ~text:"move to the previous sub-expression";
xpm_label_box ~file:"icon png files/arrow-down-double-small.png" ~text:"focus" ~packing:focus_spec_button#add ();
(*previous_button#unset_image();
xpm_label_box ~file:"icon png files/arrow-down-double-small.png" ~text:"Reset" ~packing:focus_spec_button#add ();*)
tooltips#set_tip focus_spec_button#coerce ~text:"select one specification and only information regarding the specification will be displayed";
xpm_label_box ~file:"icon png files/emblem-important-small.png" ~text:"results" ~packing:show_result_button#add ();
tooltips#set_tip show_result_button#coerce ~text:"show verification results";
tooltips#set_tip core_close_button#coerce ~text:"maximize/minimize core window"
;;

let vpaned = GPack.paned `VERTICAL ~border_width:5 ~width:920 ~packing:vbox#add ()
let factory = new GMenu.factory ~accel_path:"<EDITOR>/" menubar 
let accel_group = factory#accel_group

let file_menu = factory#add_submenu "File"
let edit_menu = factory#add_submenu "Edit"
let tools_menu = factory#add_submenu "Tools"



(*the main Scrolled Window*)
let scrolled_win = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
     ~height:400
    ~packing:vpaned#add1 ()

let hbox = GPack.hbox ~packing:(vbox#pack ~expand: false) ()

 
let exp_label = 
   GMisc.label
    ~justify:`LEFT
    ~width:20
    ~height:10
    ~xalign:0.3
    ~packing:hbox#add()

let empty_label= 
   GMisc.label
    ~packing:hbox#add()

let info_label =
   GMisc.label
    ~justify:`RIGHT
    ~width: 20
    ~height:10
    ~packing:hbox#add()

(* the Info Window*)
let info_win = GBin.scrolled_window
    ~height:400
    ~packing:vpaned#add2()
let info_view = 
  GText.view
    ~packing:info_win#add()

let result_win = GWindow.window ~title:"verification results" ~position:`CENTER ()

let languages_manager = GSourceView.source_languages_manager ()

let lang =
  if use_mime_type then
    match languages_manager#get_language_from_mime_type lang_mime_type with
    | None -> failwith (sprintf "no language for %s" lang_mime_type)
    | Some lang -> lang
  else
    match
      GSourceView.source_language_from_file ~languages_manager lang_file
    with
    | None -> failwith (sprintf "can't load %s" lang_file)
    | Some lang -> lang

let core_languages_manager = GSourceView.source_languages_manager ()

let core_lang =
  if use_mime_type then
    match core_languages_manager#get_language_from_mime_type lang_mime_type with
    | None -> failwith (sprintf "no language for %s" lang_mime_type)
    | Some lang -> lang
  else
    match
      GSourceView.source_language_from_file ~languages_manager core_lang_file
    with
    | None -> failwith (sprintf "can't load %s" lang_file)
    | Some lang -> lang

let highlight (st:GText.iter) (en:GText.iter) (tag:string) (buffer:GSourceView.source_buffer)= buffer#apply_tag_by_name tag st en

let remove_highlight (tag_name: string)(buffer:GSourceView.source_buffer)= buffer#remove_tag_by_name tag_name buffer#start_iter buffer#end_iter

let highlight_range (st:int) (en:int) (tag:string) (buffer:GSourceView.source_buffer)=
			let start_iter = buffer#get_iter (`OFFSET st) in
			let end_iter = buffer#get_iter (`OFFSET en) in
			highlight start_iter end_iter tag buffer

class editor ?packing ?show() = object (self)
  val source_view =
    GSourceView.source_view
      ~auto_indent:true
       ~insert_spaces_instead_of_tabs:true ~tabs_width:2
      ~show_line_numbers:true
      ~margin:80 ~show_margin:true
      ~smart_home_end:true
      ~highlight_current_line:true
      ~packing:scrolled_win#add (*~height:500 ~width:650*)
      ()

  val core_view = GSourceView.source_view
      ~auto_indent:true
       ~insert_spaces_instead_of_tabs:true ~tabs_width:2
      ~show_line_numbers:true
      ~margin:80 ~show_margin:true
      ~smart_home_end:true
      ~highlight_current_line:true
      ~editable:true
      ~packing:core_scrolled_win#add ~height:800 ~width:0
      ()


  val core_win = GWindow.window ~title:"Core"()
  val mutable filename = None
  val mutable cprog = None
  val mutable iprog = None
  val mutable curr_elist = None
  val mutable curr_ilist = None
  val control_win = GWindow.window (*~kind:`POPUP *)~title:"Control Window" ()
  val info_win = GWindow.window ~kind:`POPUP ~title:"Information Window" ~type_hint: `TOOLBAR ~position:`MOUSE (*~width: 50 *)~height:25 ()
  val mutable cprinter = false;
  val exp_in_elist = ref(-1);
  val mutable curr_pd = None
  
  method control_win = control_win
  method core_win = core_win
  method info_win = info_win
  method core_view = core_view

  method source_view = source_view
  
  method filename = filename
  method cprog = cprog
  method iprog = iprog
  method scrolled_win = GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~packing:core_win#add()

  method process_source_full source =
  
  prerr_endline (sprintf "\nProcessing file \"" ^ source ^ "\""); 
  let _ = Util.push_time "Preprocessing" in
  let prog = parse_file_full source in
	  let _ = prerr_endline (sprintf ("Translating global variables to procedure parameters...")) in
	  let intermediate_prog = Globalvars.trans_global_to_param prog in
	       iprog <- Some intermediate_prog;
	  let _ = prerr_endline (sprintf "Translating to core language...") in
	  let cur_cprog = Astsimp.trans_prog intermediate_prog in
	  (*let _ = ignore(Typechecker.check_prog cur_cprog) in*)
	  (*let core_str = Cprinter.string_of_program cur_cprog in*)
		cprog <- Some cur_cprog; 
		if !Globals.verify_callees then begin
		  let tmp = Cast.procs_to_verify cur_cprog !Globals.procs_verified in
			Globals.procs_verified := tmp
		end;
		ignore(Typechecker.check_prog cur_cprog);
		cur_cprog
  
  method show_core_win () =
     core_view#source_buffer#set_language core_lang;
     core_view#source_buffer#set_highlight true;(*core_win#show();core_view <- Some view;view*)

  method string_of_false_ctx_pos (a:string)(c:Globals.loc) = a^" ("^(string_of_int c.Globals.start_pos.Lexing.pos_lnum)^","^
		( string_of_int (c.Globals.start_pos.Lexing.pos_cnum-c.Globals.start_pos.Lexing.pos_bol))^") "

  method highlight_false_ctx (fclist:loc list) =
	match fclist with
	|fc::rest -> let st = fc.start_pos.pos_cnum in
		     let en = fc.end_pos.pos_cnum in
		     let st_line = fc.start_pos.pos_lnum in
		     let en_line = fc.end_pos.pos_lnum in
		     highlight_range st en "deadcode_highlight" source_view#source_buffer;self#highlight_false_ctx rest;
		     prerr_endline(sprintf "false ctx st_line:%i, st_column:%i; en_line:%i, en_column:%i" st_line (st-fc.start_pos.pos_bol+1) en_line (en-fc.end_pos.pos_bol+1))
	|[] ->()

  method search_marker name =
	match source_view#source_buffer#get_first_marker with	
	|Some first_marker -> self#search_marker_iter name first_marker
	|None -> raise Not_found

  method search_marker_iter name cur_marker =
	match source_view#source_buffer#get_last_marker with	
	|Some last_marker -> if (last_marker#get_name = cur_marker#get_name && (not (name = cur_marker#get_name)))then raise Not_found
	else if (cur_marker#get_name = name) then cur_marker
	else self#search_marker_iter name cur_marker#next
	|None -> raise Not_found

  method search_marker_list (name:string) (marker_list:GSourceView.source_marker list) = match marker_list with
	|[] -> raise Not_found
	|m::[] -> (*prerr_endline (sprintf "%s" m#get_name);*)if (m#get_name = name) then m else raise Not_found
	|m::rest -> prerr_endline (sprintf "name?");prerr_endline (sprintf "%s" m#get_name);if (m#get_name = name) then m else self#search_marker_list name rest

  method change_exp (info:string) (core_l:Cast.core_loc) (ename) (pd) = 
  let label = core_l.Cast.state in
  if (fst(!focused_prepost) = 0) then begin
		    info_view#buffer#set_text info; Cslink.highlight_exp core_l source_view#source_buffer; exp_label#set_text ename;Cslink.highlight_poscons pd.Cast.proc_static_specs source_view#source_buffer label end
			else begin info_view#buffer#set_text (sprintf "Focusing on pre with id: %i\n%s" (snd(!focused_prepost)) info); Cslink.highlight_exp core_l source_view#source_buffer; exp_label#set_text ename; 
			Cslink.highlight_poscon (snd(!focused_prepost)) pd.Cast.proc_static_specs source_view#source_buffer "focus_highlight"; remove_highlight "light_blue_highlight" source_view#source_buffer; end
				
 
  method get_full_err_list e spec_strl (e_l, d_l) =
	match spec_strl with
	|[]->(e_l,d_l)
	|s::rest ->  let e_l,d_l = Cast.err_fail_list e s (e_l,d_l) in
		self#get_full_err_list e rest (e_l,d_l)

 method highlight_err_exp (l:Cast.core_loc) =
	let color = ref("") in
        (*remove_highlight "yellow_highlight" buffer;
        remove_highlight "red_highlight" buffer;
        remove_highlight "old_fail_highlight" buffer;*)
	
	(Hashtbl.iter (fun e (v_pre, v_exc, v_post, fail_trace) -> 
		List.iter (fun (trace,flag) -> 
			if (flag == true) then color := "init_err_highlight"
			else color := ("init_old_fail_highlight")) fail_trace) l.state); 
     if not(!color = ("")) then highlight_range (l.pos.Globals.start_pos.Lexing.pos_cnum) (l.pos.Globals.end_pos.Lexing.pos_cnum) !color source_view#source_buffer


 method highlight_err_loc (fclist:Cast.core_loc list) =
	match fclist with
	|fc::rest -> self#highlight_err_exp fc; self#highlight_err_loc rest
	|[] ->()

  method highlight_err (err_l:Cast.exp list) =
	match err_l with
	|[]->()
	| e::rest -> let (info,core_l,ename) = (Cslink.string_of_exp_label e (snd(!focused_prepost))) in
			self#highlight_err_exp core_l; self#highlight_err rest

  method highlight_err_proc (proc:Cast.proc_decl) =
	let specs = proc.proc_static_specs in
	let spec_str_list = Cslink.lbl_list specs in
	match proc.proc_body with
	|None -> ()
	|Some exp -> let e_l,d_l = self#get_full_err_list exp spec_str_list ([],[]) in
			self#highlight_err e_l

  method highlight_err_procs (procs:Cast.proc_decl list) = 
	match procs with
	|[]->()
	|p::rest -> self#highlight_err_proc p; self#highlight_err_procs rest

  method highlight_all_err () = match cprog with
   |None -> ()
   |Some core -> self#highlight_err_procs core.prog_proc_decls

  method print_exp_info (pos:GText.iter) = curr_elist <- None; exp_in_elist := -1;
			match cprog with
			     |None -> prerr_endline(sprintf "not to core yet")
			     |Some core ->let offset = pos#offset in
					let pd = Cslink.look_up_proc_loc core.Cast.prog_proc_decls offset in
					let elist = ref([]:Cast.exp list) in
					let ilist = ref([]:Iast.exp list) in
					match pd.Cast.proc_body with 
           | Some e -> let _ = Cslink.set_elist e elist offset in
		   (*let _ = Islink.set_elist e ilist offset in*)
		   let length = (List.length !elist) in
		   curr_elist <- Some elist;
		   curr_pd <- Some pd;
		   (*curr_ilist <- Some ilist;*)
		   if not(List.length !elist == 0) then begin
		   let exp1 = List.hd !elist in 
		   let (info,core_l,ename) = (Cslink.string_of_exp_label exp1 (snd(!focused_prepost))) in
		   let label = core_l.Cast.state in
			if (fst(!focused_prepost) == 0) then begin
		    info_view#buffer#set_text info; Cslink.highlight_exp core_l source_view#source_buffer; exp_label#set_text ename; exp_in_elist:=0;
		    Cslink.highlight_poscons pd.Cast.proc_static_specs source_view#source_buffer label end
			else begin info_view#buffer#set_text (sprintf "Focusing on pre with id: %i\n%s" (snd(!focused_prepost)) info); Cslink.highlight_exp core_l source_view#source_buffer; exp_label#set_text ename; exp_in_elist:=0;
			Cslink.highlight_poscon (snd(!focused_prepost)) pd.Cast.proc_static_specs source_view#source_buffer "focus_highlight"; remove_highlight "light_blue_highlight" source_view#source_buffer; end
		   end
		   else begin remove_highlight "yellow_highlight" source_view#source_buffer;remove_highlight "red_highlight" source_view#source_buffer;remove_highlight "old_fail_highlight" source_view#source_buffer; exp_label#set_text "No Expression Selected"(*; self#highlight_false_ctx !Globals.false_ctx_line_list*) end
	   | None   -> info_view#buffer#set_text "no expression\n"

  method elist_length ()= match curr_elist with
	|Some elist -> List.length !elist
	|None -> -1
(*num can only be -1 or 1 to zoom in and out*)
  method get_exp_in_elist (num:int) = match curr_elist with
	|None -> exp_label#set_text "No Expression Selected"
	|Some exp_list-> if (List.length !exp_list == 0) then exp_label#set_text "No Expression Selected"
			else let num_required = !exp_in_elist+num in
                             let curr_exp = List.nth !exp_list !exp_in_elist in
			     let curr_l = Cast.pos_of_exp curr_exp in
				if ( num_required>= 0 && num_required < List.length !exp_list) then begin
				let (info,core_l,ename) = (Cslink.string_of_exp_label (List.nth !exp_list num_required) (snd(!focused_prepost))) in
	if (num > 0) then begin
		if not(curr_l.Globals.start_pos.Lexing.pos_cnum <= core_l.Cast.pos.Globals.start_pos.Lexing.pos_cnum & curr_l.Globals.end_pos.Lexing.pos_cnum >= core_l.Cast.pos.Globals.end_pos.Lexing.pos_cnum) then begin
		match curr_pd with
		|Some pd->
		  self#change_exp info core_l ename pd; exp_in_elist := num_required 
		|None -> prerr_endline "Not in a procedure" end 
		else if (num_required+num < self#elist_length()) then begin exp_in_elist:= num_required;  self#get_exp_in_elist (num) end end
	else begin
		if not(curr_l.Globals.start_pos.Lexing.pos_cnum >= core_l.Cast.pos.Globals.start_pos.Lexing.pos_cnum & curr_l.Globals.end_pos.Lexing.pos_cnum <= core_l.Cast.pos.Globals.end_pos.Lexing.pos_cnum) then begin
		match curr_pd with
		|Some pd->
		  self#change_exp info core_l ename pd; exp_in_elist := num_required 
		|None -> prerr_endline "Not in a procedure" end 
		else if (num_required+num >= 0) then begin exp_in_elist:= num_required; self#get_exp_in_elist (num) end end
end 

  method show_control_win ()= 
        try
	(*let control_win = GWindow.window (*~kind:`POPUP *)~title:"Control Window" ()in*)
	let con_vbox = GPack.vbox ~packing:control_win#add() in
	let con_hbox1 = GPack.hbox ~packing:con_vbox#add () in
	let con_hbox2 = GPack.hbox ~packing:con_vbox#add () in
	let con_hbox3 = GPack.hbox ~packing:con_vbox#add () in
	let choose_printer = GButton.toggle_button ~label:"original_printer" ~packing:(con_hbox3#pack ~padding:10) () in
	choose_printer#connect#toggled ~callback:(fun() -> if (cprinter = true) then begin cprinter <-false end else cprinter<- true);
	let lbutton = GButton.button ~packing:(con_hbox1#pack ~padding:5) () in
	let larrow = GMisc.arrow ~kind:`LEFT ~shadow:`ETCHED_IN ~packing: lbutton#add () in
	let rbutton = GButton.button ~packing:(con_hbox1#pack ~padding:5) () in
	let rarrow = GMisc.arrow ~kind:`RIGHT ~shadow:`ETCHED_OUT ~packing:rbutton#add() in
	
	let ubutton = GButton.button ~packing:(con_hbox1#pack ~padding:5) () in
	let uarrow = GMisc.arrow ~kind:`UP ~shadow:`IN ~packing: ubutton#add () in
	let dbutton = GButton.button ~packing:(con_hbox1#pack ~padding:5) () in
	let darrow = GMisc.arrow ~kind:`DOWN ~shadow:`OUT ~packing:dbutton#add() in

	let next_button = GButton.button ~label:"next" ~packing:(con_hbox2#pack ~padding:5) () in
	
	let core_button = GButton.button ~label:"core" ~packing:(con_hbox2#pack ~padding:5) () in
	let link_button = GButton.button ~label:"link" ~packing:(con_hbox2#pack ~padding:5) () in
	let exp_button = GButton.button ~label:"cur exp" ~packing:(con_hbox2#pack ~padding:5) () in

	link_button#connect#clicked ~callback:(fun() -> if (cprinter = false) then begin match cprog with
							     |None -> prerr_endline(sprintf "not to core yet")
							     |Some core ->let pos = self#curr_pos () in
							let offset = pos#offset in
							let pd = Cslink.look_up_proc_loc core.Cast.prog_proc_decls offset in
							let name = pd.Cast.proc_name in
							
							let st_loc_mark = Cprinter3.search_mark_list ("pd_"^name^"_st") !Cprinter3.loc_mark_list in
							let en_loc_mark = Cprinter3.search_mark_list ("pd_"^name^"_en") !Cprinter3.loc_mark_list in
							(*let st_mark = st_loc_mark.Cprinter3.iter_pos in
							let en_mark = en_loc_mark.Cprinter3.iter_pos in*)
							let st_iter = core_view#source_buffer#get_iter (`OFFSET st_loc_mark.Cprinter3.loc_offset) in
							let en_iter = core_view#source_buffer#get_iter (`OFFSET en_loc_mark.Cprinter3.loc_offset) in
							let blue = core_view#source_buffer#create_tag [`BACKGROUND "blue"] in
							prerr_endline (sprintf "start iter line:%i, end iter line:%i" st_iter#line en_iter#line);
							core_view#source_buffer#apply_tag blue st_iter en_iter end
);

	(*move left*)
  	lbutton#connect#clicked ~callback:(fun () -> let pos =source_view#source_buffer#get_iter `INSERT in
					self#print_left_pos();
					source_view#source_buffer#place_cursor (pos#backward_cursor_position)
					);
  	(*move right*)
  	rbutton#connect#clicked ~callback:(fun () -> try (if (List.length !Islink.exp_stack = 0) then begin let pos =source_view#source_buffer#get_iter `INSERT in
					match iprog with
	  		|Some intermediate -> 
				let pos = self#curr_pos() in
	 			 let offset = pos#offset in
				let proc = Islink.look_up_proc_loc (intermediate.Iast.prog_proc_decls) offset in
				(match proc.Iast.proc_body with
				|Some exp -> (*Cslink.exp_stack := ref([]:Cast.exp list); *)Islink.init_exp_stack exp;
				   let next_exp = Islink.next_exp1 () in
				   let next_pos = Islink.move_to_exp next_exp source_view#source_buffer in
				   let next_iter = (source_view#source_buffer#get_iter (`OFFSET next_pos)) in
					(*Cslink.exp_pop;*)
					source_view#source_buffer#place_cursor next_iter;self#print_exp_info next_iter;
					prerr_endline (Iprinter.string_of_exp next_exp)
				|None ->prerr_endline ("procedure body is empty"))
			
	  		|None -> prerr_endline (sprintf "haven't processed core yet")end
		else begin  let next_exp = Islink.next_exp1 () in 
			let next_pos = Islink.move_to_exp  next_exp source_view#source_buffer in
			let next_iter = (source_view#source_buffer#get_iter (`OFFSET next_pos)) in
					(*Cslink.exp_pop;*)
					source_view#source_buffer#place_cursor next_iter;self#print_exp_info next_iter;prerr_endline (Iprinter.string_of_exp next_exp) end)
	 with Islink.Wrong_type (s) -> (prerr_endline (sprintf "no more exp in the proc")));
  	(*move up*)
  	ubutton#connect#clicked ~callback:(fun () -> (self#get_exp_in_elist 1));

  	(*move down*)
  	dbutton#connect#clicked ~callback:(fun () -> (self#get_exp_in_elist (-1)));

  	core_button#connect#clicked ~callback:(fun() -> match filename with 
  								|None -> prerr_endline (sprintf "no source specified");
								|Some source -> 
								        Buffer.clear Astsimp.prim_buffer;
									
									let core = self#process_source_full source in
									let _ = self#show_core_win() in
									if (cprinter = false) then begin Cprinter3.string_of_program core core_view#source_buffer; self#highlight_false_ctx !Globals.false_ctx_line_list;end
									else begin
										let text = Cprinter.string_of_program core in
											core_view#source_buffer#set_text text;self#highlight_false_ctx !Globals.false_ctx_line_list;
									end
										);
	
	control_win#show();
        with _-> prerr_endline (sprintf "Contrl Window already opened")

  method link_core () = if (cprinter = false) then begin match cprog with
							     |None -> prerr_endline(sprintf "not to core yet")
							     |Some core ->let pos = self#curr_pos () in
		let _ = remove_highlight "light_blue_highlight" core_view#source_buffer in
		let offset = pos#offset in
		let pd = Cslink.look_up_proc_loc core.Cast.prog_proc_decls offset in
		let name = pd.Cast.proc_name in
							
		let st_loc_mark = Cprinter3.search_mark_list ("pd_"^name^"_st") !Cprinter3.loc_mark_list in
		let en_loc_mark = Cprinter3.search_mark_list ("pd_"^name^"_en") !Cprinter3.loc_mark_list in
		let st_iter = core_view#source_buffer#get_iter (`OFFSET st_loc_mark.Cprinter3.loc_offset) in
		let en_iter = core_view#source_buffer#get_iter (`OFFSET en_loc_mark.Cprinter3.loc_offset) in
		(*let blue = core_view#source_buffer#create_tag [`BACKGROUND "blue"] in*)
		highlight_range st_iter#offset en_iter#offset "light_blue_highlight" core_view#source_buffer end

  method matching_bracket () =
    let iter = source_view#source_buffer#get_iter_at_mark `INSERT in
    match GSourceView.find_matching_bracket iter with
    | None -> prerr_endline "no matching bracket"
    | Some iter ->
        source_view#source_buffer#place_cursor iter;
        source_view#misc#grab_focus ()

  method set_focus() = 
	focused_prepost := (0,-1); remove_highlight "focus_highlight" source_view#source_buffer

  method focus_on_prepos () =
	let (start_iter, end_iter) = source_view#source_buffer#selection_bounds in
	let start_offset = start_iter#offset in
	let end_offset = end_iter#offset in
	(*if (start_offset == end_offset) then prerr_endline "Please select a boundary"	*)
	match cprog with
	|Some c -> let id = Cslink.get_poscon_id start_offset end_offset c.Cast.prog_proc_decls in
		if (id == (-1)) then prerr_endline "Please select a valid pre-post condition"
		else focused_prepost := (1,id); prerr_endline (sprintf "id:%ia" id); info_view#buffer#set_text (sprintf "Focusing on pre with id: %i\n" id)
	|None -> prerr_endline "open a source file please"

  method string_of_failed_proc (str:string list) = 
	match str with
	|[] -> ""
	|s::rest -> s^self#string_of_failed_proc rest

  method show_results () = if not(List.length !Globals.failed_proc_string = 0) then begin let str = self#string_of_failed_proc !Globals.failed_proc_string in  
	let result_view = GText.view ~editable:false ~cursor_visible:false ~packing:result_win#add()in 
result_view#buffer#set_text str; result_win#show() end
	else begin let str = "\nAll procedures satisfy their post-conditions\n" in
         let result_view = GText.view ~editable:false ~cursor_visible:false ~packing:result_win#add()in 
result_view#buffer#set_text str; result_win#show() end

  method load_file name =
    try     
      (*self#start_up();*)
      let text =
          let ic = open_in name in
          let size = in_channel_length ic in
          let buf = String.create size in
          really_input ic buf 0 size;
          close_in ic;
          buf
       in
	prerr_endline(sprintf "%s\n" name);
       source_view#source_buffer#set_text text;
       filename <- Some name;
       win#set_title (sprintf "%s - Automated Verification System_TEST" name);
       Buffer.clear Astsimp.prim_buffer;
	Tpdispatcher.set_tp "om";
	Globals.print_verified_core := true;
	Globals.spec_label_count := 0;
        Globals.failed_proc_string := ([]:string list);
	Globals.false_ctx_line_list := ([] : Globals.loc list);
	let core = self#process_source_full name in
	let _ = core_view#source_buffer#set_text "" in
	let _ = Cprinter3.string_of_program core core_view#source_buffer in
		remove_highlight "red_highlight" source_view#source_buffer;
		remove_highlight "init_err_highlight" source_view#source_buffer;
		remove_highlight "err_pre_highlight" source_view#source_buffer;
		remove_highlight "old_fail_highlight" source_view#source_buffer;
		remove_highlight "init_old_fail_highlight" source_view#source_buffer;
		remove_highlight "yellow_highlight" source_view#source_buffer;
		remove_highlight "light_blue_highlight" source_view#source_buffer;
		remove_highlight "deadcode_highlight" source_view#source_buffer;
		self#highlight_false_ctx !Globals.false_ctx_line_list; 
		self#highlight_all_err();		
		self#show_results()
    with _ -> prerr_endline (sprintf "Load failed:%s" name)

  method open_file () = file_dialog ~title:"Open" ~callback:self#load_file ()

  method save_dialog () =
    file_dialog ~title:"Save" ?filename
      ~callback:(fun file -> self#output ~file) ()

  method save_file () =
    match filename with
      Some file -> self#output ~file
    | None -> self#save_dialog ()

  method output ~file =
    try
      if Sys.file_exists file then Sys.rename file (file ^ "~");
      let s = source_view#source_buffer#get_text () in
      let oc = open_out file in
      output_string oc (Glib.Convert.locale_from_utf8 s);
      close_out oc;
      filename <- Some file;
      Buffer.clear Astsimp.prim_buffer;Globals.spec_label_count := 0;
	Tpdispatcher.set_tp "om";	
	Globals.print_verified_core := true;	
	Globals.failed_proc_string := ([]:string list);
	Globals.false_ctx_line_list := ([] : Globals.loc list);
	let core = self#process_source_full file in
	let _ = core_view#source_buffer#set_text "" in
	let _ = Cprinter3.string_of_program core core_view#source_buffer in
	let pos = self#curr_pos() in
		remove_highlight "red_highlight" source_view#source_buffer;
		remove_highlight "init_err_highlight" source_view#source_buffer;
		remove_highlight "err_pre_highlight" source_view#source_buffer;
		remove_highlight "old_fail_highlight" source_view#source_buffer;
		remove_highlight "init_old_fail_highlight" source_view#source_buffer;
		remove_highlight "yellow_highlight" source_view#source_buffer;
		remove_highlight "light_blue_highlight" source_view#source_buffer;
		remove_highlight "deadcode_highlight" source_view#source_buffer;
	    self#highlight_false_ctx !Globals.false_ctx_line_list; self#print_exp_info pos;
	    self#highlight_all_err();self#show_results()
    with _ -> prerr_endline "Save failed"

(* get cursor position *)  
   method  print_line_pos ()=
     let iter =source_view#source_buffer#get_iter_at_mark `INSERT in
     let ori_text = info_view#buffer#get_text ()in
     info_view#buffer#set_text (sprintf "%scursor position:(%i,%i)\n" ori_text (iter#line+1) (iter#line_index+1)) 

   method print_pos (iter:GText.iter) = info_label#set_text (sprintf "Line %i,Column %i\n" (iter#line+1) (iter#line_index+1));

   method print_curr_pos () = 
     let iter =source_view#source_buffer#get_iter_at_mark `INSERT in
     self#print_pos iter;

   method print_clicked_pos () = 
     let win = match source_view#get_window `WIDGET with
	  | None -> assert false
	  | Some w -> w
	in
	let x,y = Gdk.Window.get_pointer_location win in
	let b_x,b_y = source_view#window_to_buffer_coords ~tag:`WIDGET ~x ~y in
	let clicked_pos = source_view#get_iter_at_location ~x:b_x ~y:b_y in
	self#print_pos clicked_pos; self#print_exp_info clicked_pos;clicked_pos

   method start_up ()=
     source_view#misc#modify_font_by_name font_name;

     (* set red as foreground color for definition keywords *)
     let id = "Definition@32@keyword" in
     let st = lang#get_tag_style id in
     st#set_foreground_by_name "red";
     lang#set_tag_style id st;

     (* set a style for bracket matching *)
     source_view#source_buffer#set_check_brackets true;
     let _ =
       let st = GSourceView.source_tag_style
	   ~background_by_name:"green"
	   ~foreground_by_name:"yellow"
	   ~bold: true
	   ()
       in
       source_view#source_buffer#set_bracket_match_style st
     in
     source_view#source_buffer#set_language lang;
     source_view#source_buffer#set_highlight true;
     source_view#source_buffer#create_tag ~name:"red_highlight" [`BACKGROUND "red"];
     source_view#source_buffer#create_tag ~name:"init_err_highlight" [`BACKGROUND "red"];
     source_view#source_buffer#create_tag ~name:"err_pre_highlight" [`BACKGROUND "#FFCCFF"];
     source_view#source_buffer#create_tag ~name:"focus_highlight" [`BACKGROUND "#FFCCFF"];
     source_view#source_buffer#create_tag ~name:"old_fail_highlight" [`BACKGROUND "#FFCCFF"];
     source_view#source_buffer#create_tag ~name:"init_old_fail_highlight" [`BACKGROUND "#FFCCFF"];
     source_view#source_buffer#create_tag ~name:"yellow_highlight" [`BACKGROUND "#FFFF00"];
     source_view#source_buffer#create_tag ~name:"light_blue_highlight" [`BACKGROUND "#CCCCFF"];
     source_view#source_buffer#create_tag ~name:"deadcode_highlight" [`BACKGROUND "#FF6600"];
     source_view#source_buffer#create_tag ~name:"red_underline" [`FOREGROUND "red"; `UNDERLINE `SINGLE];
     source_view#source_buffer#create_tag ~name:"underline" [`UNDERLINE `DOUBLE];
     core_view#source_buffer#set_language core_lang;
     core_view#source_buffer#set_highlight true;
     info_view#buffer#set_text "Welcome to our Automated Verification System!";
     filename <- Some "unknown.ss";
     
   
   method skip (pos:GText.iter) =
	match pos#forward_search "}" with
	|Some (cl_start, cl_end) -> source_view#source_buffer#place_cursor cl_end; (*self#skip curr_pos;*)
	|None -> prerr_endline (sprintf "not found");

   method print_left_pos () = 
      let pos = self#curr_pos () in self#print_pos pos#backward_cursor_position;pos#backward_cursor_position

   method print_right_pos () = 
      let pos = self#curr_pos () in self#print_pos pos#forward_cursor_position;pos#forward_cursor_position
   
   method curr_pos () = self#source_view#source_buffer#get_iter `INSERT;

   method move_up () = 
     let pos = self#curr_pos() in
     let pos_offset = pos#line_offset in
	self#source_view#source_buffer#place_cursor (pos#backward_line);
	let new_pos = self#source_view#source_buffer#get_iter `INSERT in
	if (pos_offset <= new_pos#chars_in_line) then begin 
             self#source_view#source_buffer#place_cursor (new_pos#set_line_offset pos_offset); end
	else self#source_view#source_buffer#place_cursor (new_pos#forward_to_line_end);
	self#print_curr_pos();

   method move_down () =
     let pos = self#curr_pos() in
	let pos_offset = pos#line_offset in
	self#source_view#source_buffer#place_cursor (pos#forward_line);
	let new_pos = self#source_view#source_buffer#get_iter `INSERT in
	if (pos_offset <= new_pos#chars_in_line) then begin 
	self#source_view#source_buffer#place_cursor (new_pos#set_line_offset pos_offset); end
	else self#source_view#source_buffer#place_cursor (new_pos#forward_to_line_end);
	self#print_curr_pos()

 
    (*Use "String.make n c"?*)
    method string_of_space (level:int) = 
        match level with
        |0 -> ""
        |_ -> "\t\t"^self#string_of_space (level - 1)
 
    (*indentation of core*)
    method indent (str:string) (level:int)=
        (*match str with
        |[(line:string);'\n';(rest:string)] -> ""
        | _->""*)
        if (String.contains str '\n') then begin 
		(*let len = String.length str in*)
		let index = String.index str '\n' in
		let (line,rest) = self#break_str str index in
		let line = self#remove_front_space line in
		if (String.contains line '{' && String.contains line '}')then begin
			let (brack, another) = self#break_str line (String.index line '}') in
			self#string_of_space level^brack^"\n"^self#indent (another^rest) level
		end
		else if (String.contains line '{' (*&& not (String.contains line '(' && (String.index line '(') = ((String.index line '{')+1))*)) then begin
			(*prerr_endline (sprintf "{?"^line);*)
			self#string_of_space level^line^self#indent rest (level+1)
		end
		else if (String.contains line '}' (*&& not (String.contains line ')' && (String.index line ')') <= ((String.index line '}')-1))*))then begin
			(*prerr_endline (sprintf "}?"^line);*)
			if (String.index line '}'=0) then
			self#string_of_space (level-1)^line^self#indent rest (level-1)
			else
			let index = String.index line '}' in
			let length = String.length line in
			self#string_of_space level^(String.sub line 0 index)^"\n"^(String.sub line (index) (length - index))^self#indent rest (level-1)
		end
		else begin
			self#string_of_space level^line^self#indent rest level
		end
        end
        else begin self#string_of_space level^str end

    method break_str (str:string) (index:int) =
	let len = String.length str in
	let line = String.sub str 0 (index+1) in
	let rest = String.sub str (index+1) (len-index-1) in
	();(line,rest)

   method remove_front_space (str:string) = 
	if not (String.contains str ' ') then str
	else if (String.index str ' ' != 0) then str
	else self#remove_front_space (String.sub str 1 ((String.length str)-1))

end

let editor = new editor ~packing:scrolled_win#add()



let string_of_movement_tag mtag= 
    match mtag with
       |`PAGES -> "pages"
       |`BUFFER_ENDS -> "buffer ends"
       | `DISPLAY_LINES -> "display lines"
       | `DISPLAY_LINE_ENDS -> "display line ends"
       | `LOGICAL_POSITIONS -> "logical positions"
       | `PARAGRAPHS -> "paragraphs"
       | `PARAGRAPH_ENDS -> "paragraph ends"
       | `VISUAL_POSITIONS -> "visual_position"
       | `WORDS -> "words"
      | _ -> "otherwise"





(*Main*)
let _ =
  win#set_allow_shrink true;
  editor#start_up();
  win#connect#destroy (fun _ -> GMain.quit ());
  let factory = new GMenu.factory ~accel_path:"<EDITOR File>/////" file_menu ~accel_group 
  in
  factory#add_item "Open" ~key:_o ~callback:editor#open_file;
  factory#add_item "Save" ~key:_S ~callback:editor#save_file;
  factory#add_item "Save as..." ~callback:editor#save_dialog;
  factory#add_separator ();
  factory#add_item "Quit" ~key:_Q ~callback:win#destroy;
  let factory = new GMenu.factory ~accel_path:"<EDITOR File>///" edit_menu ~accel_group in
  factory#add_item "Copy" ~key:_C ~callback:
    (fun () -> editor#source_view#source_buffer#copy_clipboard GMain.clipboard);
  factory#add_item "Cut" ~key:_X ~callback:
    (fun () -> GtkSignal.emit_unit
        editor#source_view#as_view GtkText.View.S.cut_clipboard);
  factory#add_item "Paste" ~key:_V ~callback:
    (fun () -> GtkSignal.emit_unit
        editor#source_view#as_view GtkText.View.S.paste_clipboard);
 
 (*factory#add_separator ();
  factory#add_check_item "Word wrap" ~active:false ~callback:
    (fun b -> editor#source_view#set_wrap_mode (if b then `WORD else `NONE));
  factory#add_check_item "Read only" ~active:false
    ~callback:(fun b -> editor#source_view#set_editable (not b));*)

  factory#add_item "Undo" ~key:_Z ~callback:editor#source_view#source_buffer#undo;
  factory#add_item "Redo" ~key:_Y ~callback:editor#source_view#source_buffer#redo;
  let factory = new GMenu.factory ~accel_path:"<EDITOR File>/" tools_menu ~accel_group in
  factory#add_item "Match Bracket" ~key:_M ~callback:editor#matching_bracket;
  factory#add_item "Get Cursor Position" ~key:_P ~callback:editor#print_line_pos;
  factory#add_item "Focus on pre-post" ~callback:editor#focus_on_prepos;
  factory#add_item "Reset focus" ~callback:editor#set_focus;
  win#add_accel_group accel_group;

  

  (*button_press means left click(1), right click(3) or middle (2) of the mouse*)
  editor#source_view#event#connect#button_press
    ~callback:(fun ev ->  
	  let _ = Islink.exp_stack := ([]:Iast.exp list) in
      let b_types =  GdkEvent.Button.button in
      let button = b_types ev in
      if button = 3 then begin
        file_menu#popup ~button ~time:(GdkEvent.Button.time ev); true
      end else if (button = 1 && GdkEvent.get_type ev = `BUTTON_PRESS) then begin
        editor#print_clicked_pos();
	false; (*"false" means the default event signal still happens*)
      end (*else if (button = 2) then begin editor#info_win#destroy ();editor#info_win#show ();
	let win = match editor#source_view#get_window `WIDGET with
	  | None -> assert false
	  | Some w -> w
	in
	let x,y = Gdk.Window.get_pointer_location win in
	let x_origin, y_origin = Gdk.Window.get_position (Gdk.Window.get_parent win) in
	(*prerr_endline (sprintf "x_origin: %i, y_origin: %i" x_origin y_origin);*)
	editor#info_win#move (x_origin+x) (y_origin+y);
	let pos_iter = editor#print_clicked_pos() in
		editor#source_view#source_buffer#place_cursor pos_iter;true end*)
      else begin prerr_endline (sprintf "%i" button);false end);

   (*double clicks:single press->single release->single press->double press->single release*)
   editor#source_view#event#connect#button_press
    ~callback:(fun ev ->   
      if (GdkEvent.Button.button ev = 1 &&
      GdkEvent.get_type ev = `TWO_BUTTON_PRESS) then begin
          prerr_endline (sprintf "double clicked");
	  let buffer = editor#source_view#source_buffer in
	  let pos = editor#curr_pos() in
	  let offset = pos#offset in
	  let cprog = editor#cprog in
	  let _ = Islink.exp_stack := ([]:Iast.exp list) in
	  (*prerr_endline(sprintf "offset:%i" offset);*)
	  remove_highlight "yellow_highlight" buffer;
	  match cprog with
	  |Some core -> let proc = Cslink.look_up_proc_loc (core.Cast.prog_proc_decls) offset in
			let (startp,endp) = Cslink.get_proc_range proc in
			(*let tag = highlight_tag buffer "yellow" in*)
			(*prerr_endline(sprintf "name:%s\n start:%i end:%i" proc.proc_name startp endp);*)
			highlight_range startp endp "yellow_highlight" buffer;true
	  |None -> prerr_endline (sprintf "haven't processed core yet");true
(*status_win#show();*)
      end else false);

   (*key press*)
   editor#source_view#event#connect#key_press
    ~callback:(fun ev -> 
      let key = GdkEvent.Key.hardware_keycode ev in
	  let _ = Islink.exp_stack := ([]:Iast.exp list) in
      if (key = 113) then begin
        let pos = editor#print_left_pos() in
	editor#print_exp_info pos;
        (*prerr_endline (sprintf "keycode: %i" (GdkEvent.Key.hardware_keycode ev));*)false;
      end else if (key = 114) then begin
        let pos = editor#print_right_pos() in
	editor#print_exp_info pos;false;
      end else if (key = 111) then begin
        editor#move_up();
	editor#print_exp_info (editor#curr_pos());true;
      end else if (key = 116) then begin
        editor#move_down();
	editor#print_exp_info (editor#curr_pos());true;
      end else false);
	
  core_close_button#connect#clicked ~callback:(fun a ->if (larrow#kind = `LEFT) then begin (editor#core_view#misc#set_size_request ~width:0 (); vpaned#misc#set_size_request ~width:920 (); larrow#set_kind `RIGHT)end else begin editor#core_view#misc#set_size_request ~width:350 (); vpaned#misc#set_size_request ~width:600 (); larrow#set_kind `LEFT end);

  next_button#connect#clicked ~callback:(fun () -> try (if (List.length !Islink.exp_stack = 0) then begin let pos =editor#source_view#source_buffer#get_iter `INSERT in
					match editor#iprog with
	  		|Some intermediate -> 
				let pos = editor#curr_pos() in
	 			 let offset = pos#offset in
				let proc = Islink.look_up_proc_loc (intermediate.Iast.prog_proc_decls) offset in
				(match proc.Iast.proc_body with
				|Some exp -> (*Cslink.exp_stack := ref([]:Cast.exp list); *)Islink.init_exp_stack exp;
				   let next_exp = Islink.next_exp1 () in
				   let next_pos = Islink.move_to_exp next_exp editor#source_view#source_buffer in
				   let next_iter = (editor#source_view#source_buffer#get_iter (`OFFSET next_pos)) in
					(*Cslink.exp_pop;*)
					editor#source_view#source_buffer#place_cursor next_iter;editor#print_exp_info next_iter;editor#print_pos next_iter(*;
					prerr_endline (Iprinter.string_of_exp next_exp)*)
				|None ->prerr_endline ("procedure body is empty"))
			
	  		|None -> prerr_endline (sprintf "haven't processed core yet")end
		else begin  let next_exp = Islink.next_exp1 () in 
			let next_pos = Islink.move_to_exp  next_exp editor#source_view#source_buffer in
			let next_iter = (editor#source_view#source_buffer#get_iter (`OFFSET next_pos)) in
					(*Cslink.exp_pop;*)
					editor#source_view#source_buffer#place_cursor next_iter;editor#print_exp_info next_iter;(*prerr_endline (Iprinter.string_of_exp next_exp);*)editor#print_pos next_iter end)
	 with Islink.Wrong_type (s) -> (prerr_endline (sprintf "no more exp in the proc")));

  previous_button#connect#clicked ~callback:(fun () -> 
	if not(List.length !Islink.prev_exp_stack = 0) then begin
	let prev_exp = Islink.prev_exp () in 
			let next_pos = Islink.move_to_exp  prev_exp editor#source_view#source_buffer in
			let next_iter = (editor#source_view#source_buffer#get_iter (`OFFSET next_pos)) in
					(*Cslink.exp_pop;*)
					editor#source_view#source_buffer#place_cursor next_iter;editor#print_exp_info next_iter;(*prerr_endline (Iprinter.string_of_exp next_exp);*)editor#print_pos next_iter 
	end);

  open_file_button#connect#clicked ~callback:(editor#open_file);
  save_file_button#connect#clicked ~callback:(editor#save_file);
  zoom_out_button#connect#clicked ~callback:(fun () -> (editor#get_exp_in_elist 1));
  zoom_in_button#connect#clicked ~callback:(fun () -> (editor#get_exp_in_elist (-1)));
  show_result_button#connect#clicked ~callback:(fun () -> editor#show_results ());
  focus_spec_button#connect#clicked ~callback:(fun () -> if not(focus_spec_button#active) then begin editor#set_focus ();info_view#buffer#set_text ""; editor#print_exp_info (editor#curr_pos()) end else begin editor#focus_on_prepos (); editor#print_exp_info (editor#curr_pos())end);

  win#show ();
  (*editor#show_control_win();*)
  GMain.Main.main ();


  
