#include "xdebug.cppo"
open VarGen
open Globals
open Solver
open Cast


module CP = Cpure
module CF = Cformula



let enable_gui = Scriptarguments.enable_gui
let label_counter = ref 0

type item_kind = 
  |ItemProc
  |ItemPrec
  |ItemPost
  |ItemAssert
  |ItemScall
  |ItemBind

type pre_entry = {
ctx:Cformula.context;
spec:Cformula.ext_formula
}

type item_entry = {
  kind:item_kind;
  pos:loc;
  proc:proc_decl;
  pre: pre_entry option;
  obl:Cformula.struc_formula option;
  lpath : path_trace list
}


let string_of_path_trace (p_tr: path_trace) : string =
  "[" ^ (String.concat "," (List.map (fun (c1,c3)-> "(" ^ (Cprinter.string_of_formula_label c1 "") ^ " " ^ (string_of_int c3) ^ ")" ) p_tr)) ^ "]  "

let invappend l1 l2 = List.append l2 l1

let is_obl_fail (ctx_list : Cformula.list_context list) : bool =
  if ctx_list = [] then false
  else
    List.for_all Cformula.isFailCtx ctx_list


class mainwindow title namef = 
  let infotbl = Hashtbl.create 30 in
  let window =  GWindow.window ~title ~border_width:5  ~width:980 ~height:730 () in
  let h_main_paned = GPack.paned `HORIZONTAL ~packing:window#add () in 
  let left_scrolled_window = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC () in
  let right_vpaned = GPack.paned `VERTICAL () in
  let top_right_scrolled_window = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC () in
  let top_right_view = GText.view ~editable:false ~packing:top_right_scrolled_window#add () in
  let bot_right_scrolled_window = GBin.scrolled_window ~hpolicy:`AUTOMATIC  ~vpolicy:`AUTOMATIC  () in
  let code_source_view = GSourceView2.source_view ~auto_indent:true
    ~insert_spaces_instead_of_tabs:true ~tab_width:2 ~show_line_numbers:true
    ~show_right_margin:false ~editable:false 
    ~smart_home_end:`ALWAYS ~highlight_current_line:true ~packing:bot_right_scrolled_window#add ~height:280 ~width:100
    ~border_width:2 () in
  let code_language_manager = GSourceView2.source_language_manager ~default:true in
  let obl_cols =  new GTree.column_list in
  let col_obl_id = obl_cols#add Gobject.Data.int in
  let col_obl_name = obl_cols#add Gobject.Data.string in
  let col_obl_stat = obl_cols#add Gobject.Data.string in
  let obl_store = GTree.tree_store obl_cols in 
  let obl_view_c1 = GTree.view_column ~title:"Obligations" ~renderer:(GTree.cell_renderer_text [`FONT "Monospace 11"], ["text", col_obl_name]) () in
  let obl_view_c2 = GTree.view_column ~title:"Status" ~renderer:(GTree.cell_renderer_text [`FOREGROUND "RED"; `FOREGROUND_SET true; `FONT "Monospace 12"], ["text", col_obl_stat]) () in
object (self)
  val filename = namef
  val font_name = "Monospace 10"
  val lang_mime_type = "text/x-ss"
  val mutable obl_view = GTree.view ~model:obl_store ~packing:(left_scrolled_window#add_with_viewport) ()
  val mutable view_source = GText.view ()
    (* val mutable counter = 0 *)
  val mutable prog = None
  val mutable  source_code_bookmark = None



  method private init_source_view () =

    let text = 
      let ic = open_in filename in
      let size = in_channel_length ic in
      let buf = String.create size in
	really_input ic buf 0 size;
	close_in ic;
	buf
    in

    let lang = 
      match code_language_manager#guess_language ~content_type:lang_mime_type () with
          Some x -> x
    	| None -> failwith (Printf.sprintf "no language for source code")
    in
      code_source_view#misc#modify_font_by_name font_name;
      code_source_view#source_buffer#set_highlight_matching_brackets true;
      code_source_view#set_show_line_marks true;
      code_source_view#source_buffer#set_language (Some lang);
      code_source_view#source_buffer#set_highlight_syntax true;
      code_source_view#source_buffer#set_text text;
      self#init_source_code_bookmark ()



  method private init_source_code_bookmark () =
    let category = "curent" in
      source_code_bookmark <- Some (code_source_view#source_buffer#create_source_mark ~category (code_source_view#source_buffer#get_iter `START)); 
      let pixbuf =  code_source_view#misc#render_icon ~size:`DIALOG `ZOOM_IN in
	code_source_view#set_mark_category_background ~category (Some (GDraw.color (`NAME "light green")));
	code_source_view#set_mark_category_pixbuf ~category (Some pixbuf);



  method private set_code_source_pos line  =
    let nr_lines = code_source_view#source_buffer#line_count in
    let vscroll_upp = bot_right_scrolled_window#vadjustment#upper in
    let vscroll_pgsize = bot_right_scrolled_window#vadjustment#page_size in 
      bot_right_scrolled_window#vadjustment#set_value ((float_of_int line)*.((vscroll_upp -. vscroll_pgsize)/. (float_of_int nr_lines)));
      match source_code_bookmark with 
	  None -> begin
	    self#init_source_code_bookmark ();
	    self#set_code_source_pos line
	  end
	| Some crt_bookmark -> 	code_source_view#source_buffer#move_mark crt_bookmark#coerce ~where:(code_source_view#source_buffer#get_iter (`LINE line))
	    
	    

  method private set_left () = 
    h_main_paned#pack1 ?resize:(Some true) ?shrink:(Some true) (left_scrolled_window#coerce)


  method private set_right () = 
    self#init_source_view ();
    right_vpaned#pack1 ?resize:(Some true) ?shrink:(Some true) (top_right_scrolled_window#coerce);
    right_vpaned#pack2 ?resize:(Some true) ?shrink:(Some true) (bot_right_scrolled_window#coerce);
    h_main_paned#pack2 ?resize:(Some true) ?shrink:(Some true) (right_vpaned#coerce)
      


  method private display_top_right txt = 
    let buffer = top_right_view#buffer in
      buffer#set_text txt





  method private obl_sel_changed () =
    let selection = obl_view#selection in
    let pr path =
      let row = obl_store#get_iter path in
      let crt_id = obl_store#get ~row ~column:col_obl_id in
      let crt_name = obl_store#get ~row ~column:col_obl_name in
      let { kind=crt_kind; pos=crt_pos; proc=crt_proc;pre=crt_pre;obl=crt_obl;lpath=paths} = Hashtbl.find infotbl crt_id in
      let crt_line = crt_pos.start_pos.Lexing.pos_lnum in
	self#set_code_source_pos (crt_line -1); 
	Printf.printf "\n\nPATHS at LINE %s  :  %s"  (string_of_int crt_pos.start_pos.Lexing.pos_lnum) (String.concat " " (List.map string_of_path_trace paths)); 
        flush stdout;
	match crt_kind with
	    ItemProc -> begin
	      (* Printf.printf "Procedure = (%d, %s)\n" crt_id crt_name; *)
	      (* Printf.printf "DISPLAY POSITION (in left bottom win) %s\n" (Debug.string_of_pos crt_pos); *)
	      (* flush stdout; *)
	      self#display_top_right (crt_name ^ "\n\n" ^ (Cprinter.string_of_struc_formula crt_proc.proc_static_specs))
	    end
	  |ItemPrec ->  begin
	      (* Printf.printf "Precondition = (%d, %s)\n" crt_id crt_name; *)
	      (* Printf.printf "DISPLAY POSITION (in left bottom win) %s\n" (Debug.string_of_pos crt_pos); *)
	      (* flush stdout; *)
	      match crt_pre with
		  None -> 
		    self#display_top_right (crt_name ^ "\n\n")
		|Some pre1 -> 
		   self#display_top_right (crt_name ^ "\n\n" ^ (Cprinter.string_of_context pre1.ctx))
	    end
	     
	  |ItemPost ->  begin
	      (* Printf.printf "Postcondition = (%d, %s)\n" crt_id crt_name; *)
	      (* Printf.printf "DISPLAY POSITION (in left bottom win) %s\n" (Debug.string_of_pos crt_pos); *)
	      (* flush stdout *)
	      match crt_pre with
		  None -> 
		    self#display_top_right (crt_name ^ "\n\n")
		|Some pre1 -> 
		   self#display_top_right (crt_name ^ "\n\n" ^ (Cprinter.string_of_ext_formula pre1.spec))
	    end
	  |ItemAssert
	  |ItemScall
	  |ItemBind -> begin
	      (* Printf.printf "Obligation = (%d, %s)\n" crt_id crt_name; *)
	      (* Printf.printf "DISPLAY POSITION (in left bottom win) %s\n" (Debug.string_of_pos crt_pos); *)
	      (* flush stdout *)
	      match crt_obl with
		  None -> 
		    self#display_top_right (crt_name ^ "\n\n")
		|Some obl1 -> 
		   self#display_top_right (crt_name ^ "\n\n" ^ (Cprinter.string_of_struc_formula obl1))
	    end
	     
    in
      try
	List.iter pr selection#get_selected_rows
      with Not_found -> begin
	print_string "current selection is invalid\n"; 
	exit 1
      end


  method private obl_reasons (crt_row: Gtk.tree_iter) =
    let crt_id = obl_store#get ~row:crt_row ~column:col_obl_id in
      (* let crt_name = obl_store#get ~row:crt_row ~column:col_obl_name in *)
    let rs_list = Solver.entail_hist#get crt_id in
      (* print_string ("\nOBLIGATION: " ^ crt_name ^ ": entries in entail_hist: " ^ (string_of_int (List.length rs_list)) ^"\n\n"); *)
      (* flush stdout; *)
      if not (is_obl_fail rs_list) then self#upd_obl_status crt_row "SUCCESS" else self#upd_obl_status crt_row "FAIL";


  method private upd_all_obls_status (prec_row: Gtk.tree_iter) = 
    (* print_string ("\nUpdating all the obligations\n");  *)
    (* flush stdout; *)
    if (obl_store#iter_has_child prec_row) then begin
      let crt_row = obl_store#iter_children (Some prec_row) in
      let flag = ref true in
  	while !flag do
	  self#obl_reasons crt_row;
  	  flag := obl_store#iter_next crt_row
  	done
    end else begin
      print_string ("\nNO Obligations for the current SPEC\n"); 
      flush stdout
    end





      

  method private obl_sel_double_click path col1 =
    let row = obl_store#get_iter path in
    let crt_id = obl_store#get ~row ~column:col_obl_id in
    let crt_name = obl_store#get ~row ~column:col_obl_name in
      try
	let { kind=crt_kind; pos=crt_pos; proc=crt_proc; pre=crt_pre; obl=crt_obl; lpath=paths } = Hashtbl.find infotbl crt_id in
	  match crt_kind with
	    | ItemProc -> begin
		Printf.printf "(NO SUPPORT) START ANALYIS on Procedure (all specs) = (%d, %s)\n" crt_id crt_name;
		flush stdout
	      end
	    |ItemPrec -> begin
		match crt_pre with
		  | None -> begin
		      Printf.printf "CANNOT START ANALYIS on Procedure with one spec= %s. NO PRECONDITION\n" crt_name;
		      flush stdout
		    end
		  | Some pre1 -> begin 
		      match crt_proc.proc_body with
			| None -> ()
			| Some body -> begin
			    self#upd_obl_status row "  WORKING";
			    Solver.entail_hist#init ();  
			    try
			      Printf.printf "START ANALYIS on Procedure with one spec =  %s\n" crt_name;
			      flush stdout;
			      let result = Typechecker.check_specs (self#get_prog ()) crt_proc pre1.ctx [pre1.spec] body in
				if result then begin	
				  print_string ("\nProcedure "^crt_proc.proc_name^" SUCCESS\n"); flush stdout;
				  self#upd_obl_status row "  SUCCESS";  
				end
				else begin	
				  print_string ("\nProcedure "^crt_proc.proc_name^" FAIL\n"); flush stdout;
				  self#upd_obl_status row "  FAIL"
				end;
				self#upd_all_obls_status row
			    with _ -> begin
			      print_string ("\nProcedure "^crt_proc.proc_name^" FAIL (exception)\n"); flush stdout;
			      self#upd_obl_status row "  FAIL";
			      self#upd_all_obls_status row
			    end
			  end
		    end
	      end
	       
	    |ItemPost
	    |ItemAssert
	    |ItemScall
	    |ItemBind -> begin
		Printf.printf "CANNOT START ANALYIS on an obligation (%d, %s)\n" crt_id crt_name;
		flush stdout
	      end
      with Not_found -> begin
	print_string "current selection is invalid\n"; 
	exit 1
      end

  method private init_obl_tree_view  () =
    ignore(obl_view#append_column obl_view_c1);
    ignore(obl_view#append_column obl_view_c2);
    obl_view#selection#set_mode `BROWSE;
    obl_view#set_rules_hint true;
    ignore(obl_view#connect#row_activated ~callback:(self#obl_sel_double_click));
    ignore(obl_view#selection#connect#changed ~callback:(self#obl_sel_changed))

  method set_prog (prog1 : prog_decl) =
    prog <- Some prog1

  method get_prog () =
    match prog with
	None -> begin 
	  print_string "prog is not initialized\n"; 
	  exit 1
	end
      |Some p -> p


  method upd_obl_status  (row: Gtk.tree_iter) (name : string)  =
    obl_store#set ~row ~column:col_obl_stat name
      

  method add_proc name (proc1 : proc_decl) :Gtk.tree_iter = 
    let crt_row = obl_store#append () in
    let proc_item = {kind = ItemProc; pos = proc1.proc_loc; proc=proc1; pre = None; obl = None; lpath =[]} in
      Globals.branch_point_id :=  !Globals.branch_point_id + 1;
      let counter = !Globals.branch_point_id in 
	Hashtbl.add infotbl counter proc_item;
	obl_store#set ~row:crt_row ~column:col_obl_id counter; 
	obl_store#set ~row:crt_row ~column:col_obl_name ("PROCEDURE  "^ name);
	obl_store#set ~row:crt_row ~column:col_obl_stat " ";
	crt_row


  method add_post (paths: path_trace list) (crt_row : Gtk.tree_iter) : Gtk.tree_iter = 
    let crt_id = obl_store#get ~row:crt_row ~column:col_obl_id in
    let { kind=crt_kind; pos=crt_pos; proc=crt_proc;pre=crt_pre;obl=crt_obl;lpath=_} = Hashtbl.find infotbl crt_id in
    let name = "POSTCONDITION " in 
    let post_item = {kind = ItemPost; pos = crt_pos; proc=crt_proc; pre = crt_pre; obl = crt_obl; lpath=paths } in
      match crt_pre with
	| Some {ctx=_;spec=Cformula.EAssume (x,b,y,t)} -> begin
	    let counter = fst y in
	    let post_row = obl_store#append ~parent:crt_row () in
	      Hashtbl.add infotbl counter post_item;
  	      obl_store#set ~row:post_row ~column:col_obl_id counter;
  	      obl_store#set ~row:post_row ~column:col_obl_name  name; (*(name ^ " Label(" ^ (string_of_int counter) ^ ")"); *)
  	      obl_store#set ~row:post_row ~column:col_obl_stat " ";
	      post_row
	  end
	| _ -> begin 
	    print_string "spec is invalid\n"; 
	    exit 1
	  end


  method add_spec (proc1 : proc_decl) (crt_row : Gtk.tree_iter) (pre1 : pre_entry) : Gtk.tree_iter =    
    match pre1.spec with
      | Cformula.ECase b -> begin 
	  print_string "spec is invalid\n"; 
	  exit 1
	end
      | Cformula.EBase b -> begin 
	  print_string "spec is invalid\n"; 
	  exit 1
	end
      | Cformula.EAssume (x,b,y,t)-> begin 
	  let pos1 = Cformula.pos_of_formula b in
	  let name = "PRECONDITION at Line " ^ (string_of_int pos1.start_pos.Lexing.pos_lnum) in 
	  let pre_item = {kind = ItemPrec; pos = pos1; proc=proc1; pre = (Some pre1); obl = None; lpath=[] } in
	    Globals.branch_point_id :=  !Globals.branch_point_id + 1; 
	    let counter = !Globals.branch_point_id * 1000 in 
	      iast_label_table := ((Some (counter,"")),"proc_spec",[],pos1) ::!iast_label_table;
	      let pre_row = obl_store#append ~parent:crt_row () in
		Hashtbl.add infotbl counter pre_item;
  		obl_store#set ~row:pre_row ~column:col_obl_id counter;
  		obl_store#set ~row:pre_row ~column:col_obl_name name;
  		obl_store#set ~row:pre_row ~column:col_obl_stat " ";
		pre_row
	end

	  
  method add_obl (k:item_kind) (name:string) (proc1 : proc_decl) (obl1 : Cformula.struc_formula) (pos1 : loc) (pid:formula_label) (paths: path_trace list) (crt_row : Gtk.tree_iter) : Gtk.tree_iter =
    let obl_row = obl_store#append ~parent:crt_row () in
    let obl_item = {kind = k; pos = pos1; proc=proc1; pre = None; obl = (Some obl1); lpath=paths} in
    let obl_id = fst pid in
      Hashtbl.add infotbl obl_id obl_item;
      obl_store#set ~row:obl_row ~column:col_obl_id obl_id;
      obl_store#set ~row:obl_row ~column:col_obl_name name; (* (name ^ " Label(" ^ (string_of_int obl_id) ^ ")"); *)
      obl_store#set ~row:obl_row ~column:col_obl_stat " ";  
      obl_row


  method private init () =
    window#set_allow_shrink true;
    self#init_obl_tree_view ();
    self#set_left (); 
    self#set_right ()

  method show () = 
    self#init ();
    window#show ()

  initializer ignore(window#connect#destroy ~callback:GMain.Main.quit)  
end


(* ---------------------------------------------------------------------------- *)


 let app_win = ref None


 let get_win () =
   match !app_win with
       None -> begin 
	 print_string "application window is not initialized\n"; 
	 exit 1
       end
     |Some w -> w

 let set_win (w:mainwindow) =
   app_win := Some w
 

 (* ------------------  COLLECT OBLIGATIONS ------------------------- *)
 (* ---------------- following the typechecker code------------------ *)


 
 let rec check_specs (prog : prog_decl) (proc : proc_decl) (ctx : CF.context) spec_list : pre_entry list = 
   let rec do_spec_verification (spec: Cformula.ext_formula) : pre_entry list = 
     match spec with
       | Cformula.ECase b -> List.concat (List.map (fun (c1,c2)-> 
						      let nctx = CF.transform_context (combine_es_and prog c1 true) ctx in
							check_specs prog proc nctx c2) b.Cformula.formula_case_branches)
       | Cformula.EBase b ->
	   let nctx = Cformula.normalize_max_renaming_s b.Cformula.formula_ext_base b.Cformula.formula_ext_pos false ctx in
	     check_specs prog proc nctx b.Cformula.formula_ext_continuation 
	       
       | Cformula.EAssume (x,b,y,_) -> [{ctx=ctx; spec=spec}]
	   
   in	
     List.concat (List.map do_spec_verification spec_list)


 let rec check_exp (w:mainwindow) (spec_iter_list :Gtk.tree_iter list) (prog : prog_decl) (proc : proc_decl) (crt_paths: path_trace list) e0  : path_trace list = 
   match e0 with
     |Assert ({exp_assert_asserted_formula = c1_o;
               exp_assert_assumed_formula = c2;
               exp_assert_path_id = (pid,s);
               exp_assert_type = t;
               exp_assert_pos = pos}) -> (
         match c1_o with
         | None -> crt_paths
         | Some c1 -> (
             let str = match t with
               | None -> "ASSERT"
               | Some true -> "ASSERT_EXACT"
               | Some false -> "ASSERT_INEXACT" in
             ignore (List.map (w#add_obl ItemAssert (str ^" at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum)) proc c1 pos (pid,s) crt_paths) spec_iter_list);
             crt_paths
           )
       )
     | Assign ({exp_assign_lhs = v;
   		exp_assign_rhs = rhs;
   		exp_assign_pos = pos}) -> check_exp w spec_iter_list prog proc crt_paths rhs

     | Bind ({exp_bind_type = body_t;
   	      exp_bind_bound_var = (v_t, v);
   	      exp_bind_fields = lvars;
   	      exp_bind_body = body;
	      exp_bind_path_id = pid;
   	      exp_bind_pos = pos}) -> begin
   	 let field_types, vs = List.split lvars in
   	 let v_prim = CP.SpecVar (v_t, v, Primed) in
   	 let vs_prim = List.map2 (fun v -> fun t -> CP.SpecVar (t, v, Primed)) vs field_types in
   	 let p = CP.fresh_spec_var v_prim in
   	 let c = string_of_typ v_t in
   	   (* let vdatanode = CF.DataNode ({CF.h_formula_data_node = (if !Globals.large_bind then p else v_prim); *)
   	   (* 			       CF.h_formula_data_name = c; *)
   	   (* 			       CF.h_formula_data_arguments =  vs_prim; *)
   	   (* 			       CF.h_formula_data_pos = pos}) in *)

	 let vdatanode = CF.DataNode ({CF.h_formula_data_node = (if !Globals.large_bind then p else v_prim);
				       CF.h_formula_data_name = c;
				       CF.h_formula_data_arguments = (*t_var :: ext_var ::*) vs_prim;
				       CF.h_formula_data_label = None;
               CF.h_formula_data_pure_annot = None;
				       CF.h_formula_data_pos = pos}) in
   	 let vheap = CF.formula_of_heap vdatanode pos in
	   match pid with
	       None -> begin
		 print_string ("no LABEL for Bind at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum));
		 exit 1
	       end
	     | Some ppid -> begin
		 (* print_string (Cprinter.string_of_formula_label ppid (("BIND at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum)) ^ "\n\n"));flush stdout; *)
   		 ignore (List.map (w#add_obl ItemBind ("BIND at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum)) proc (CF.formula_to_struc_formula vheap) pos ppid crt_paths) spec_iter_list);
   		 check_exp w spec_iter_list prog proc crt_paths body
	       end

       end

     | Block ({exp_block_type = t;
   	       exp_block_body = e;
   	       exp_block_local_vars = local_vars;
   	       exp_block_pos = pos}) ->  check_exp w spec_iter_list prog proc crt_paths e

     | Cond ({exp_cond_type = t;
   	      exp_cond_condition = v;
   	      exp_cond_then_arm = e1;
   	      exp_cond_else_arm = e2;
	      exp_cond_path_id =pid;
   	      exp_cond_pos = pos}) -> begin
	 match pid with 
	     None -> begin
	       print_string ("no LABEL for COND at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum));
	       exit 1
	     end
	   | Some ppid -> begin 
	       (* label_counter := !label_counter +1; *)
	       (* let nA = (string_of_int !label_counter) ^ "A: IF at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum) in *)
	       (* let nB = (string_of_int !label_counter) ^ "B: IF at line "  ^ (string_of_int pos.start_pos.Lexing.pos_lnum) in *)
	       (* let a_iter_list = List.map (w#add_label nA proc pos) spec_iter_list in *)
	       (* let b_iter_list = List.map (w#add_label nB proc pos) spec_iter_list in *)
	       
   	       let paths1 = check_exp w spec_iter_list prog proc (List.map (invappend [(ppid,0)]) crt_paths) e1 in
		 (* Printf.printf "COND 1PATHS: %d\n\n"  (List.length paths1); (\* (String.concat ";" (List.map string_of_path_trace paths)); *\) *)
		 (* flush stdout; *)
	       let paths2 = check_exp w spec_iter_list prog proc (List.map (invappend [(ppid,1)]) crt_paths) e2 in
		 (* Printf.printf "COND 2PATHS: %d\n\n"  (List.length paths2); (\* (String.concat ";" (List.map string_of_path_trace paths)); *\) *)
		 (* flush stdout; *)
		 paths1 @ paths2
	     end
       end
     | SCall ({exp_scall_type = ret_t;
     	       exp_scall_method_name = mn;
     	       exp_scall_arguments = vs;
     	       exp_scall_visible_names = p_svars;
	       exp_scall_path_id = pid;
     	       exp_scall_pos = pos}) -> begin
     	 let proc1 = look_up_proc_def pos prog.prog_proc_decls mn in
     	   (* let l_iter_list = *)
	   match pid with
	       None -> begin
		 print_string ("no LABEL for CALL at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum));
		 exit 1
	       end
	     | Some ppid -> begin
		 (* print_string (Cprinter.string_of_formula_label ppid (("CALL at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum)) ^ "\n\n"));flush stdout; *)
		 ignore (List.map (w#add_obl ItemScall ("CALL method " ^ mn ^ " at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum)) 
             proc (* proc1.proc_static_specs_with_pre *) (proc1.proc_stk_of_static_specs # top) pos ppid crt_paths) spec_iter_list);
		 crt_paths 
	       end
		 (* in () *)
		 (* let ftypes, fnames = List.split proc1.proc_args in *)
		 (* let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in *)
		 (* let nox = CF.formula_of_pure (CF.no_change fsvars proc1.proc_loc) proc1.proc_loc in *)
		 (* let init_form = nox in *)
		 (* let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) proc1.proc_loc in *)
		 (* let init_ctx = CF.build_context init_ctx1 init_form proc1.proc_loc in *)
		 (* let spec_list = check_specs prog proc1 init_ctx (proc1.proc_static_specs_with_pre) in *)
		 (*   (\* let spec_list = Cformula.split_struc_formula proc1.proc_static_specs_with_pre  *\) *)
		 (*   label_counter := !label_counter +1; *)
		 (*   let ch = int_of_char 'A' in *)
		 (*   let do_one_iter  iter =  *)
		 (*     let rec do_one_spec lst c = *)
		 (*       match lst with *)
		 (* 	   [] -> () *)
		 (* 	 |s::ls ->  begin *)
		 (* 	     ignore(w#add_label_call ((string_of_int !label_counter) ^ (String.make 1 (char_of_int c)) ^ ": Specification") proc pos s iter); *)
		 (* 	     do_one_spec ls (c+1) *)
		 (* 	   end *)

       (*     in *)
       (*       do_one_spec spec_list ch *)

       (*   in *)
       (*     List.iter do_one_iter l_iter_list *)
       end

     | Seq ({exp_seq_type = te2;
   	     exp_seq_exp1 = e1;
   	     exp_seq_exp2 = e2;
   	     exp_seq_pos = pos}) -> begin
   	 let paths1= check_exp w spec_iter_list prog proc crt_paths e1 in
   	   check_exp w spec_iter_list prog proc paths1 e2
       end

     | Try ({exp_try_body = body;
     	     exp_catch_clause = cc;
	     exp_try_path_id = pid;
     	     exp_try_pos = pos })-> begin
	 (* label_counter := !label_counter +1; *)
	 (* let nA = (string_of_int !label_counter) ^ "A: TRY-CATCH at line " ^ (string_of_int pos.start_pos.Lexing.pos_lnum) in *)
	 (* let nB = (string_of_int !label_counter) ^ "B: TRY-CATCH at line "  ^ (string_of_int pos.start_pos.Lexing.pos_lnum) in *)
	 (* let a_iter_list = List.map (w#add_label nA proc pos) spec_iter_list in *)
	 (* let b_iter_list = List.map (w#add_label nB proc pos) spec_iter_list in *)
   	 let paths_1 = check_exp w spec_iter_list prog proc crt_paths body in
   	 let paths_2 = check_exp w spec_iter_list prog proc paths_1 cc.exp_catch_body in
	   paths_1 @ paths_2
       end

     | Label e -> 
	 check_exp w spec_iter_list prog proc crt_paths e.exp_label_exp

     | _ -> crt_paths



 let check_proc (w:mainwindow) (prog : prog_decl) (proc : proc_decl)  =
   let unmin_name = unmingle_name proc.proc_name in
   let check_flag = ((Gen.is_empty !procs_verified) || List.mem unmin_name !procs_verified)
     && not (List.mem unmin_name !Inliner.inlined_procs)
   in
     if check_flag then begin
       match proc.proc_body with
	 | None -> ()
	 | Some body -> begin
             let proc_iter = w#add_proc unmin_name proc in 
	     let ftypes, fnames = List.split proc.proc_args in
	     let fsvars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
	     let nox = CF.formula_of_pure (CF.no_change fsvars proc.proc_loc) proc.proc_loc in
	     let init_form = nox in
	     let init_ctx1 = CF.empty_ctx (CF.mkTrueFlow ()) proc.proc_loc in
	     let init_ctx = CF.build_context init_ctx1 init_form proc.proc_loc in
	     let spec_list = check_specs prog proc init_ctx (proc.proc_static_specs @ proc.proc_dynamic_specs) in
	     let spec_iter_list =  List.map (w#add_spec proc proc_iter) spec_list in 
	     let crt_paths = check_exp w spec_iter_list prog proc [[]] body in 
	       ignore (List.map (w#add_post crt_paths) spec_iter_list)
	   end 
     end



let check_data (w:mainwindow) (prog : prog_decl) (cdef : data_decl) =
  if not (Gen.is_empty cdef.data_methods) then
    ignore(List.map (check_proc w prog) cdef.data_methods)

let check_prog (w:mainwindow) (prog : prog_decl) =
  w#set_prog prog;
  ignore (List.map (check_data w prog) prog.prog_data_decls);
  ignore (List.map (check_proc w prog) prog.prog_proc_decls)
 



