#include "xdebug.cppo"
(* Ocamlgraph RTC program: Find Biconnected component, *)
(* RTC algorithm generating extra constraints for Equality Logic*)
(* Xuan Bach-24/04/2012*)
(* We need a better Finding BCC algorithm since this significantly affects*)
(* on the efficiency of the overall*)
open Format
open Graph
open Gen.Basic

module Vt =
struct
	type t= string
	let compare= Pervasives.compare
	let hash= Hashtbl.hash
	let equal= (=)
end
module Ed =
struct
	type t= string
	let compare = Pervasives.compare
	let default = ""
end

module Ed1 =
struct
	type t= string ref
	let compare = Pervasives.compare
	let default = ref ""
end

type pairV= {ver1:string;ver2:string}	
type cell = {mutable dfs_num:int; mutable high_num: int}

module RecordPair=
	struct
		type t= pairV
		let compare = Pervasives.compare
		end
module G = Imperative.Graph.Concrete(Vt)
module Glabel = Imperative.Graph.ConcreteLabeled(Vt)(Ed1)
module Dfs= Traverse.Dfs(G)
module Adj=Oper.Neighbourhood(G)
module MapDFS=Map.Make(String) 
module MapDFSParent=Map.Make (RecordPair) 
module Clt=Cliquetree.CliqueTree(G)


(*let _= if(G.mem_edge_e g ed2) then print_endline "true" else print_endline "false" ;;*)
(*let (pt,e)= Dijkstra.shortest_path g "1" "4" in List.map (fun x->print_float ( G.E.label x)) pt;;*)

(*let l= Adj.list_from_vertex g "2" in List.map (fun x-> print_endline x) l;;*)

let max_of (x:int) (y:int)= if (x>y) then x else y

let get_var v1 v2 graph=
		try let ed=Glabel.find_edge graph v1 v2 in !(Glabel.E.label ed)
		with Not_found-> let _=print_endline_quiet ("get_var:NOT FOUND VAR!!!"^v1^" "^v2) in exit(0)

class graphFindBCC =
	object (self)
	val mutable converse_depth=0
	val mutable stack: pairV Stack.t =Stack.create ()
(*	val mutable dfs_num =MapDFS.empty(*need to be initialized later*)*)
(*	val mutable high=MapDFS.empty*)
	val mutable parents=MapDFS.empty
	val mutable bcc= G.create()
	val mutable num_ver=0
	val mutable map_list: (string,cell) Hashtbl.t=Hashtbl.create 200
	
	method find_cell s tbl=
		Hashtbl.find tbl s
	
	method init_map s =
		let c={dfs_num=0;high_num = -1} in
			let _= Hashtbl.add map_list s c in ()
			
	method add_dfs dfs_n c = 
				c.dfs_num <- dfs_n
	
	method add_high high_n c =
				c.high_num <- high_n
				
	method private findBCC graph (v11:string) (v22:string)=
		let rec loopFindBCC graph v1 v2=
			let v_dfs_num=converse_depth in
				let c=(self)#find_cell v1 map_list in
		 		let _= (self)#add_dfs v_dfs_num c in
					let _= converse_depth<-converse_depth-1 in
						let _= (self)#add_high v_dfs_num c in
(*							let _= print_endline ("In :" ^v1^ " depth: "^(string_of_int (MapDFS.find v1 dfs_num)) ^ " high: "^(string_of_int ( MapDFS.find v1 high)) ) in*)
							let neib= Adj.list_from_vertex graph v1 in
									List.map (fun w-> 
										try
										 let wc1 = (self)#find_cell w map_list in
											 let temp_edge = {ver1=v1;ver2=w} in (*modified here*)
(*												let _= print_endline ("w_dfs_num:" ^(string_of_int w_dfs_num)^ "of "^w ) in*)
												let () = if(wc1.dfs_num =0 ) then
													begin
													parents <- MapDFS.add w v1 parents;
													(* print_endline ("pushed:" ^ w ^ " " ^ v1); *)
													Stack.push temp_edge stack;
													loopFindBCC graph w v2;
(*													print_endline ("new here with current temp" ^temp_edge.ver1^temp_edge.ver2);*)
(*													let w_high = MapDFS.find w high in*)
														let wc = (self)#find_cell w map_list in	
(*													let _= print_endline ("w_high: "^ (string_of_int w_high) ^ "of "^w^" v_dfs_num: " ^(string_of_int v_dfs_num)^" of "^v1) in*)													
														let _= if(wc.high_num <= v_dfs_num & G.is_empty bcc) then
															begin
																  (*modified here*)
(*																		 let bcp=G.create() in*)
																		 let led= ref [] in	
																		 let break= ref false in 	
																		 while(!break=false) do
																			begin
(*																					let _= Stack.iter (fun x-> print_endline ("STACK " ^x.ver1^ " " ^x.ver2)) stack in*)
																				let e=Stack.pop stack in
																				(* let _= print_endline ("poped " ^ e.ver1 ^ " " ^ e.ver2)  in *)
(*																									let _= print_endline ("arti point:" ^ temp_edge.ver1) in*)
																					 let _= led := !led@[e] in   
																						let _= if(e.ver1=temp_edge.ver1 && e.ver2=temp_edge.ver2) then 
																							(let  
																							 _= if(Stack.is_empty stack & (List.length !led)>1) then
																											let _= List.map (fun e-> G.add_edge bcc e.ver1 e.ver2 ) !led in()
																									(* else print_endline ("stack not empty")		 *)
																							 in break := true)
																						in ()
																				end
																			done;
																				(* let _=G.iter_edges_e (fun x-> print_endline ("bcc:"^(G.E.src x)^" "^(G.E.dst x))) bcc in *)
(*																				let _=print_endline ("---") in*)
																				let exist_v1v2 =G.mem_edge bcc v22 v11 in 
																						let _= if(exist_v1v2=true) then ()
																							(* (print_endline ("bcc of e")) *)
																						       else 
																										(* let _= print_endline ("bcc not e") in *)
																										bcc<-G.create() in ()
																			 
																end
															in (*high <- MapDFS.add v1 (max_of w_high (MapDFS.find v1 high) ) high*) ();
(*															print_endline ("***change high of"^ v1 ^"from"^string_of_int ((MapDFS.find v1 high)) ^"to " ^(string_of_int (max_of w_high (MapDFS.find v1 high))))	;*)
															(self)#add_high (max_of wc.high_num c.high_num ) c 
														end
														else if(w <> (MapDFS.find v1 parents)) then
															let wc2=(self)#find_cell w map_list in
															if (c.dfs_num< wc2.dfs_num) then
															begin
(*																print_endline ("change high of"^ v1 ^"from"^string_of_int ((MapDFS.find v1 high)) ^"to " ^(string_of_int (max_of w_dfs_num (MapDFS.find v1 high))));*)
															  let temp_v1w={ver1=v1;ver2=w} in Stack.push temp_v1w stack;		
															  (self)#add_high (max_of wc1.dfs_num c.high_num) c 
									
															end	
(*															else print_endline ("BACK EDGE "^ w ^ " "^v1)*)
														in true
											with Not_found -> false 	
										) neib

		in loopFindBCC graph v11 v22

    method init_map_once_v2 eq_graph diseq_graph g_e=
			G.fold_vertex ( fun e i-> if((not (G.mem_vertex diseq_graph e)) && (G.in_degree eq_graph e =1))
			                          then 
																	let _= G.remove_vertex eq_graph e in 
																	let _= Glabel.remove_vertex g_e e in 
																	let _= print_endline_quiet ("got eq=1") in i
																else
						                      let _=(self)#init_map e in i+1)  eq_graph 0
		
		 method init_map_once eq_graph =
			G.fold_vertex ( fun e i-> let _=(self)#init_map e in i+1)  eq_graph 0
				
		method private subtransform graph v1 v2=
			let init_dfs_num f graph= f (fun v -> (self)#init_map v;num_ver<-num_ver+1) graph in
				let  _ = init_dfs_num Dfs.postfix graph in
				let _= converse_depth<-num_ver in
						let _= (self)#findBCC graph v1 v2 in bcc
		
		method private transform graph v1 v2 num_vertices= (*need init the map first*)
			let _= converse_depth <-num_vertices in
			let _= (self)#findBCC graph v1 v2 in bcc
		
		method return_bcc = let _= "" in bcc
		
		method getBCCSubGraph graph v1 v2 =
(*			let _=Gen.Profiling.push_time("stat_transform") in*)
			let graph = (self)#subtransform graph v1 v2 in
(*			let _=Gen.Profiling.pop_time("stat_transform") in*)
			if((G.is_empty graph )=false) then 	 
							true
			else (*let _= print_endline "No BCC found..." in*) false				
											
		method getBCCGraph graph v1 v2 num_vertices=
(*			let _=Gen.Profiling.push_time("stat_transform") in*)
			let graph = (self)#transform graph v1 v2 num_vertices in
(*			let _=Gen.Profiling.pop_time("stat_transform") in*)
			if((G.is_empty graph )=false) then 	 
							true
			else (*let _= print_endline "No BCC found..." in*) false				
		
		method add_diseq_edgev2 (graph:G.t) e =
				 if ((G.mem_vertex graph (G.E.src e)) &(G.mem_vertex graph (G.E.dst e))) then
				begin
						let _= G.add_edge_e graph e in true 
					end
				else 	false
				
(*		method add_diseq_edges (eq_graph:G.t)(diseq_graph:G.t)=      *)
(*			G.iter_edges_e (fun x->G.add_edge_e eq_graph x) diseq_graph*)
		
		method add_list_diseq_edges (eq_graph:G.t)(diseq_edges:G.E.t list)=
			List.map (fun x->G.add_edge_e eq_graph x) diseq_edges	
		
		method add_all_diseq_edges (graph:G.t)(diseq_graph:G.t)=		
			G.iter_edges_e (fun e-> G.add_edge_e graph e) diseq_graph 
			
		method print_graph graph=
			let print_graph f graph_= f (fun v -> print_endline_quiet v) graph_ in
				let  _ = print_graph Dfs.postfix graph in ()
		
		method print_chordal_graph graph=
					let print_graph_chordal f graph_= f (fun v -> let neib= Adj.list_from_vertex graph_ v in let _= let _= print_endline_quiet ("{"^v^"}")in List.map (fun x-> print_string (x^ "  {"^v^"} " )) neib in ()) graph_ in
						let  _ = print_graph_chordal Dfs.postfix graph in ()
	end;;
		
class rTC=
	object (self)
(*	val mutable allvars = G.create()*)
	val mutable number_vars=0
	val mutable local_cache : string = ""
	val mutable global_cache = G.create ()
	val bcc= new graphFindBCC
(*	val mutable g_source= Glabel.create ()*)
(*	val src= MapDFS.empty*)
	
	method make_chordal graph gr_e=
			let cpg=G.copy graph in (*traverse around the copy*)
				let dfs f graph_= f (fun v -> if((G.in_degree graph_ v)<=2) then 
																				let neib= Adj.list_from_vertex graph_ v in
																				let _= List.map (fun x-> List.map (fun k-> if(k!=x) then 
(*																					let _= print_endline ("chord here:" ^k ^ " " ^x) in*)
																					let () = G.add_edge graph_ k x in 
																					let _=G.add_edge graph k x in 
																					let mem=Glabel.mem_edge gr_e k x in 
																					if(mem=false) then 
																						let _=number_vars<-number_vars+1 and ed_var=Glabel.E.create k (ref (string_of_int number_vars)) x in Glabel.add_edge_e gr_e ed_var ) neib) neib in
																						G.remove_vertex graph_ v   
				) graph_ in 
					let  _ = dfs Dfs.postfix cpg in ()
	
	method get_var v1 v2 graph=
		try let ed=Glabel.find_edge graph v1 v2 in !(Glabel.E.label ed)
		with Not_found-> let _=print_endline_quiet ("get_var:NOT FOUND VAR!!!"^v1^" "^v2) in exit(0)
	
(*	method get_id gr_e v1 v2=*)
	method get_var_triangular v el gr_e=
		let vv1= ref "" and vv2=ref "" and v1v2= ref "" in
								let _= try vv1:= !(Glabel.E.label (Glabel.find_edge gr_e v el.ver1))  
									with Not_found->  begin let _=number_vars<-number_vars+1 and _= vv1 :=(string_of_int number_vars) in let cx1= Glabel.E.create v vv1 el.ver1 in Glabel.add_edge_e gr_e cx1 end
								in	 
								let _= try vv2:= !((Glabel.E.label (Glabel.find_edge gr_e v el.ver2))) 
											with Not_found-> begin let _=number_vars<-number_vars+1 and _= vv2 :=(string_of_int number_vars) in let cx2= Glabel.E.create v vv2 el.ver2 in Glabel.add_edge_e gr_e cx2 end
								in
								let	_= try v1v2:= !((Glabel.E.label (Glabel.find_edge gr_e el.ver1 el.ver2)))
									with Not_found -> begin let _=number_vars<-number_vars+1 and _= v1v2 :=(string_of_int number_vars) in let cx3= Glabel.E.create el.ver1 v1v2 el.ver2 in Glabel.add_edge_e gr_e cx3 end
								in (!vv1,!vv2,!v1v2)
	
	method check_in_global (vv1:G.V.t) (vv2:G.V.t) (v1v2:G.V.t)=
		try let neib_vv1= Adj.list_from_vertex global_cache vv1 in
			if(List.mem vv2 neib_vv1 ) then (List.mem v1v2 neib_vv1 )
			else false
			with exn -> false
	
	method add_to_global vv1 vv2 v1v2=
		let _=G.add_edge global_cache vv1 vv2 in
			let _=G.add_edge global_cache vv1 v1v2 in
				let _=G.add_edge global_cache vv2 v1v2 in ()
	
	method generate_constraints graph es gr_e=	
		let helper vv1 vv2 v1v2 v el= 
							(*add to local cache*)				
								let _= local_cache<- "-"^vv1^" "^"-"^vv2^" "^v1v2^" 0"^"\n"^local_cache in
(*										let _= local_cache<- "-"^vv1^" "^"-"^v1v2^" "^vv2^" 0"^"\n"^local_cache in    *)
(*												let _= local_cache<- "-"^v1v2^" "^"-"^vv2^" "^vv1^" 0"^"\n"^local_cache in*)
											let e1={ver1=v;ver2=el.ver1} and e2={ver1=v;ver2=el.ver2} in 
											(e1,e2)
								  		
		in 
		let rec loop_gc e=	
(*			let _=print_endline ("executing edge:"^e.ver1^e.ver2) in*)
			let neib_e1= Adj.list_from_vertex graph e.ver1 in
				let neib_e2=Adj.list_from_vertex graph e.ver2 in
					List.map (fun v-> if((List.mem v neib_e1)) then
							begin
							(*check local cache??*)
(*							let _= print_endline ("triangular: "^e.ver1^e.ver2^v) in*)
									begin
											let (vv1,vv2,v1v2)=	self#get_var_triangular v e gr_e in
											let check=self#check_in_global vv1 vv2 v1v2 in
												if(check=false) then
												let _=self#add_to_global vv1 vv2 v1v2 in
												let (e1,e2)=helper vv1 vv2 v1v2 v e in
												let _= loop_gc e1 and _= loop_gc e2  in ()
(*												else 	let _=print_endline "check=true" (*in let _=exit(0)*) in ()*)
									end								
							end						
					 ) neib_e2  

			 in 
			(* let _=loop_gc es in global_cache <- G.create () *) (*significantly affects on performance*)
			loop_gc es 
	
	method print_all graph =
		let _=Glabel.iter_edges_e (fun x->print_endline_quiet ("bach"^(Glabel.E.src x)^(Glabel.E.dst x)^" "^(!(Glabel.E.label x)))) graph in let _=exit(0) in () 
	
	method rm_edges_all_diseq eq_g diseq_g g_e =
			G.iter_vertex 
						(fun v->try if((G.mem_vertex eq_g v)=false) 
										then let _=G.remove_vertex diseq_g v and _=Glabel.remove_vertex g_e v in () with exn -> ((*print_endline "rm dis1"*))) diseq_g
	
	method rm_edges_degree_1 eq_g diseq_g g_e =
			let rec helper g =Glabel.iter_vertex
						(fun v-> try if((Glabel.in_degree g v)=1)
										then let _=Glabel.remove_vertex g v and _=G.remove_vertex eq_g v and _=G.remove_vertex diseq_g in helper g with exn -> ((*print_endline "rm dg1"*))) g
			in helper g_e			
																										
	method simplify_input eq_graph diseq_graph graph_e=
		let _=(self)#rm_edges_all_diseq eq_graph diseq_graph graph_e in
			self#rm_edges_degree_1 eq_graph diseq_graph graph_e 
	
	method rtc_v2 eq_graph diseq_graph graph_e num_var=
(*		let _=G.iter_edges_e (fun x->print_endline ((G.E.src x)^(G.E.dst x)^" "^(G.E.label x) )) graph_e in let _=exit(0) in*)
	  (* let _= print_endline ("RTC here!") in *)
		let _=self#simplify_input eq_graph diseq_graph graph_e in
		let num_vertices=bcc#init_map_once eq_graph in
		(* let diseq_edges= ref [] in *)
		(* let _=G.iter_edges_e (fun e-> diseq_edges := [e]@ !diseq_edges) diseq_graph in *)
		let _= number_vars<-num_var in
		let rtc_helper e= let cpg= G.copy eq_graph in 
												let check_add=bcc#add_diseq_edgev2 cpg e in
													if(check_add=true) then
(*														let _=Gen.Profiling.push_time("stat_get_BCC") in*)
														let exist_bcc=bcc#getBCCGraph cpg (G.E.dst e) (G.E.src e) num_vertices in(*BCC must contain at least 3 vertex*)
(*														let _=Gen.Profiling.pop_time("stat_get_BCC") in*)
															let _= if(exist_bcc=true) then 
															let _= bcc#add_all_diseq_edges cpg diseq_graph in
(*															let rec helper g =G.iter_vertex                                                                         *)
(*																			(fun v-> try if((G.in_degree g v)=1)                                                            *)
(*																								then let _=G.remove_vertex g v in helper g with exn -> ((*print_endline "rm dg1"*))) g*)
(*															in let _= helper cpg in	*)
																(* let _= (*if((Clt.is_chordal cpg)=false) then*)  self#make_chordal cpg graph_e in *)
(*																				let _= bcc#print_chordal_graph cpg in*)
																  let ve={ver1=(G.E.src e);ver2=(G.E.dst e)} in
(*																	let _=print_endline ("bcc of:"^(G.E.src e)^(G.E.dst e)) in*)
(*																	let _=Gen.Profiling.push_time("stat_ge_constr") in	*)
																	let _= self#generate_constraints cpg ve graph_e in
(*																	let _=Gen.Profiling.pop_time("stat_ge_constr") in*)
(*																			let _= print_endline "NEXT BCC OF DISEQ EDGE" in*)
															() in ()
		in 		
			let _=G.iter_edges_e  (fun e-> rtc_helper e) diseq_graph in 
			(* let _=print_endline ("local cache: "^local_cache) in *)
			local_cache
															
	end;;




(*		method private transform graph v1 v2=                                                                 *)
(*			let init_dfs_num f graph= f (fun v -> dfs_num <- MapDFS.add v 0 dfs_num;num_ver<-num_ver+1) graph in*)
(*				let  _ = init_dfs_num Dfs.postfix graph in                                                        *)
(*					let getBCC f graph = f (fun v->  if((MapDFS.find v dfs_num)=0) then                             *)
(*												begin                                                                             *)
(*												  converse_depth<-num_ver;                                                        *)
(*													let _= "" in (self)#findBCC graph v1 v2;                                        *)
(*													if(num_ver - converse_depth =1) then                                            *)
(*														begin                                                                         *)
(*(*															(*modified here*) print_endline "BCC contains one v"*)                    *)
(*															end                                                                         *)
(*													end                                                                             *)
(*													) graph                                                                         *)
(*						in                                                                                            *)
(*					let _= getBCC Dfs.postfix graph in bcc                                                          *)


(*
Local Variables: 
compile-command: "make -C .. bin/sudoku.opt"
End: 
*)

