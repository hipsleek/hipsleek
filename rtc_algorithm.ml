(* Ocamlgraph demo program: solving the Sudoku puzzle using graph coloring *)

open Format
open Graph
(* We use undirected graphs with nodes containing a pair of integers
   (the cell coordinates in 0..8 x 0..8).
   The integer marks of the nodes will store the colors. *)

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

type pairV= {ver1:string;ver2:string}	

module RecordPair=
	struct
		type t= pairV
		let compare = Pervasives.compare
		end
module G = Imperative.Graph.ConcreteLabeled(Vt)(Ed)
module Dfs= Traverse.Dfs(G)
module Adj=Oper.Neighbourhood(G)
module MapDFS=Map.Make(String) 
module MapDFSParent=Map.Make (RecordPair) 
module Cliq=Cliquetree.CliqueTree(G)


(*let _= if(G.mem_edge_e g ed2) then print_endline "true" else print_endline "false" ;;*)
(*let (pt,e)= Dijkstra.shortest_path g "1" "4" in List.map (fun x->print_float ( G.E.label x)) pt;;*)

(*let l= Adj.list_from_vertex g "2" in List.map (fun x-> print_endline x) l;;*)

let max_of (x:int) (y:int)= if (x>y) then x else y

class graphFindBCC =
	object (self)

	val mutable converse_depth=0
	val mutable stack: pairV Stack.t =Stack.create ()
	val mutable dfs_num =MapDFS.empty(*need to be initialized later*)
	val mutable high=MapDFS.empty
	val mutable parents=MapDFS.empty
	val mutable bcc= []
	val mutable num_ver=0

	method private findBCC graph (v1:string) (v2:string)=
		let rec loopFindBCC graph v1 v2=
			let v_dfs_num=converse_depth in
		 		let _= dfs_num <- MapDFS.add v1 v_dfs_num dfs_num in
					let _= converse_depth<-converse_depth-1 in
						let _= high <- MapDFS.add v1 v_dfs_num high in
(*							let _= print_endline ("In :" ^v1^ " depth: "^(string_of_int (MapDFS.find v1 dfs_num)) ^ " high: "^(string_of_int ( MapDFS.find v1 high)) ) in*)
							let neib= Adj.list_from_vertex graph v1 in
									List.map (fun w-> let _=
										try
										 let w_dfs_num = MapDFS.find w dfs_num in
											 let temp_edge = {ver1=v1;ver2=w} in (*modified here*)
(*												let _= print_endline ("w_dfs_num:" ^(string_of_int w_dfs_num)^ "of "^w ) in*)
												let _ = if(w_dfs_num =0 ) then
													begin
													parents <- MapDFS.add w v1 parents;
(*													print_endline ("pushed:" ^ w ^ " " ^ v1);*)
													Stack.push temp_edge stack;
													loopFindBCC graph w v2;
(*													print_endline ("new here with current temp" ^temp_edge.ver1^temp_edge.ver2);*)
													let w_high = MapDFS.find w high in
(*													let _= print_endline ("w_high: "^ (string_of_int w_high) ^ "of "^w^" v_dfs_num: " ^(string_of_int v_dfs_num)^" of "^v1) in*)
														
														let _= if(w_high <= v_dfs_num) then
															begin
																 (*modified here*)
																let  bcp= ref ([]: string list) in 
																		 let break= ref false in 	
																		 while(!break=false) do
																			begin
(*																					let _= Stack.iter (fun x-> print_endline ("STACK " ^x.ver1^ " " ^x.ver2)) stack in*)
																				 let e=Stack.pop stack in
(*																				let _= print_endline ("poped " ^ e.ver1 ^ " " ^ e.ver2)  in       *)
(*																									let _= print_endline ("arti point:" ^ temp_edge.ver1) in*)
																					  let _= bcp := [e.ver1]@[e.ver2]@ !bcp in      
																						let _= if(e.ver1=temp_edge.ver1 && e.ver2=temp_edge.ver2) then ((*print_endline ("breaked"^temp_edge.ver1^temp_edge.ver2);*)break := true)
																						in ()
																				end
																			done;
																			let _ = bcc<- !bcp 
																				in let len=List.length bcc in let exist_v1 = List.mem v1 bcc in let exist_v2= List.mem v2 bcc in
																				
(*																							let _= List.map (fun x-> print_endline x) !bcp in*)
(*																							let _= print_endline "bach" in                   *)
																						let _= if(len=2||exist_v1 =false || exist_v2=false) then bcc <-[] in ()
																			 
																			 
																end
															in (*high <- MapDFS.add v1 (max_of w_high (MapDFS.find v1 high) ) high*) ();
(*															print_endline ("***change high of"^ v1 ^"from"^string_of_int ((MapDFS.find v1 high)) ^"to " ^(string_of_int (max_of w_high (MapDFS.find v1 high))))	;*)
															high <- MapDFS.add v1 (max_of w_high (MapDFS.find v1 high) ) high
														end
														else if(w != (MapDFS.find v1 parents)) then
															begin
(*																print_endline ("change high of"^ v1 ^"from"^string_of_int ((MapDFS.find v1 high)) ^"to " ^(string_of_int (max_of w_dfs_num (MapDFS.find v1 high))));*)
															 high <- MapDFS.add v1 (max_of w_dfs_num (MapDFS.find v1 high) ) high
									
															end	
(*															else print_endline ("BACK EDGE "^ w ^ " "^v1)*)
														in true
											with Not_found -> false in ()
										) neib

		in loopFindBCC graph v1 v2

		method private transform graph v1 v2=
			let init_dfs_num f graph= f (fun v -> dfs_num <- MapDFS.add v 0 dfs_num;num_ver<-num_ver+1) graph in
				let  _ = init_dfs_num Dfs.postfix graph in
					let getBCC f graph = f (fun v->  if((MapDFS.find v dfs_num)=0) then
												begin
													converse_depth<-num_ver;
													let _= "" in (self)#findBCC graph v1 v2;
													if(num_ver - converse_depth =1) then
														begin
(*															(*modified here*) print_endline "BCC contains one v"*)
															end
													end
													) graph
						in
						let _= getBCC Dfs.postfix graph in bcc
			
		method getBCCGraph graph v1 v2 =
			let bcp = (self)#transform graph v1 v2 in
			if(bcp != []) then 
				begin
					let rem_ver f graph= f (fun v -> let exist=List.mem v bcp in if(exist=false) then G.remove_vertex graph v) graph in                                                   
         			let _= rem_ver Dfs.postfix graph in ()
					end					
			else G.clear graph				
			
		method make_chordal graph=
			let cpg=G.copy graph in 
				let dfs f graph_= f (fun v -> let neib= Adj.list_from_vertex graph_ v in
																				let _= List.map (fun x-> List.map (fun k-> if(k!=x) then 
(*																					let _= print_endline ("chord here:" ^k ^ " " ^x) in*)
																					let ed= G.E.create k "" x in let _ = G.add_edge_e graph_ ed in G.add_edge_e graph ed) neib) neib in
																						G.remove_vertex graph_ v   
				) cpg(*graph_*) in 
					let  _ = dfs Dfs.postfix cpg in ()
					
		method add_diseq_edge (graph:G.t) (x: pairV)=
			 if ((G.mem_vertex graph x.ver1) &(G.mem_vertex graph x.ver2)) then
				begin
					let ed=G.E.create x.ver1 "" x.ver2 in
						let _= G.add_edge_e graph ed in true 
					end
				else 	false
					 
		method add_list_diseq_edges (graph:G.t) (diseqs: pairV list)=
			List.map (fun x-> if ((G.mem_vertex graph x.ver1) & (G.mem_vertex graph x.ver2)) then
				begin
					let ed=G.E.create x.ver1 "" x.ver2 in
						G.add_edge_e graph ed 
					end 
			) diseqs
		
		method add_diseq_edgev2 (graph:G.t) e =
				 if ((G.mem_vertex graph (G.E.src e)) &(G.mem_vertex graph (G.E.dst e))) then
				begin
						let _= G.add_edge_e graph e in true 
					end
				else 	false
				
		method add_diseq_edges (eq_graph:G.t)(diseq_graph:G.t)=
			G.iter_edges_e (fun x->G.add_edge_e eq_graph x) diseq_graph
(*		method get_v graph v=                                                                *)
(*			if ((G.mem_vertex graph v)) then print_endline ("ex") else print_endline ("not ex")*)
		method print_graph graph=
			let print_graph f graph_= f (fun v -> print_endline v) graph_ in
				let  _ = print_graph Dfs.postfix graph in ()
		
		method print_chordal_graph graph=
					let print_graph_chordal f graph_= f (fun v -> let neib= Adj.list_from_vertex graph_ v in let _= let _= print_endline ("{"^v^"}")in List.map (fun x-> print_string (x^ "  {"^v^"} " )) neib in ()) graph_ in
						let  _ = print_graph_chordal Dfs.postfix graph in ()
	end;;


class rTC=
	object (self)
	val mutable allvars = G.create()
	val mutable local_cache = []
	val bcc= new graphFindBCC
	val mutable g_source= G.create ()
(*	val src= MapDFS.empty*)
	method generate_constraints graph e=
		let rec loop_gc e=
			let helper v= 
				let source_e1 = G.E.create v (e.ver1^e.ver2) e.ver1 in
					let source_e2= G.E.create v (e.ver1^e.ver2) e.ver2 in
						let _= G.add_edge_e g_source source_e1 in
							let _=G.add_edge_e g_source source_e2 in
							(*add to local cache*)
								let vv1= (v^e.ver1) and vv2=(v^e.ver2) and v1v2=(e.ver1^e.ver2) in
									let _=G.add_vertex allvars vv1 and _=G.add_vertex allvars vv2 and _=G.add_vertex allvars v1v2 in
										let _= local_cache<-[(vv1,vv2,v1v2)]@local_cache in
		(*						  		let _= print_endline ("Constraints in cache:---- "^(v^e.ver1)^" and "^(v^e.ver2)^" -> "^(e.ver1^e.ver2)) in *)
									  		let e1={ver1=v;ver2=e.ver1} and e2={ver1=v;ver2=e.ver2} in 
		(*								  		let _=print_endline ("edge to expand:"^v^e.ver1) in*)
		(*											 	let _=print_endline ("edge to expand:"^v^e.ver2) in																																													*)
															let _= loop_gc e1 and _= loop_gc e2 
		  in () 
		in	
(*			let _=print_endline ("executing edge:"^e.ver1^e.ver2) in*)
			let neib_e1= Adj.list_from_vertex graph e.ver1 in
				let neib_e2=Adj.list_from_vertex graph e.ver2 in
					List.map (fun v-> if((List.mem v neib_e1)) then
							begin
							(*check local cache??*)
							  let v1v2=e.ver1^e.ver2 and v2v1=e.ver2^e.ver1 and lb1=v^e.ver1 and lb11=e.ver1^v and lb2=v^e.ver2 and lb22=e.ver2^v in																													
									try let ed_e= G.find_edge g_source e.ver1 e.ver2 in
										let lbe=(G.E.label ed_e)in
																																							
										try let ed_e1=G.find_edge g_source v e.ver1 and ed_e2=G.find_edge g_source v e.ver2 in
								  		let lb_ed_e1=(G.E.label ed_e1) and lb_ed_e2=(G.E.label ed_e2) in
											if((lb_ed_e1<>v1v2 & lb_ed_e1 <>v2v1) || (lb_ed_e2<>v1v2 & lb_ed_e2<>v2v1)) then
												if(lbe<>lb1 & lbe<>lb11 & lbe<>lb2 & lbe<>lb22) then
													begin
(*														let _= print_endline ("Source FOUND edge: "^e.ver1^e.ver2^" has source:"^lbe) in*)
																helper v
														end
										with Not_found->	
											if(lbe<>lb1 & lbe<>lb11 & lbe<>lb2 & lbe<>lb22) then
													begin
(*														let _= print_endline ("Source FOUND edge: "^e.ver1^e.ver2^" has source:"^lbe) in*)
																helper v
														end			
									with Not_found->																															
(*											let _= print_endline ("Source NOT FOUND edge: "^e.ver1^e.ver2) in*)
												 helper v
							end						
					 ) neib_e2  

			 in loop_gc e
	
	
	method rtc eq_graph diseq_list =
		let _= List.map ( fun e-> let cpg= G.copy eq_graph in 
																let check_add=bcc#add_diseq_edge cpg e in
																if(check_add=true) then
																	let _=bcc#getBCCGraph cpg e.ver1 e.ver2 in
																	
																		let _= bcc#add_list_diseq_edges cpg diseq_list in 
																			let _= if((G.is_empty cpg)=false) then bcc#make_chordal cpg in
(*																				let _= bcc#print_chordal_graph cpg in*)
																			
																				let _= self#generate_constraints cpg e in
																			(*To do*)
(*																			let _= print_endline "NEXT BCC OF DISEQ EDGE" in	*)
																			()			
																	) diseq_list in local_cache
	
	method rtc_v2 eq_graph diseq_graph =
		let rtc_helper e= let cpg= G.copy eq_graph in 
												let check_add=bcc#add_diseq_edgev2 cpg e in
													if(check_add=true) then
														let _=bcc#getBCCGraph cpg (G.E.src e) (G.E.dst e) in(*BCC must contain at least 3 vertex*)
															let _= bcc#add_diseq_edges cpg diseq_graph in 
																let _= if((G.is_empty cpg)=false) then bcc#make_chordal cpg in
(*																				let _= bcc#print_chordal_graph cpg in*)
																  let ve={ver1=(G.E.src e);ver2=(G.E.dst e)} in
																	let _= self#generate_constraints cpg ve in
																(*To do*)
(*																			let _= print_endline "NEXT BCC OF DISEQ EDGE" in*)
															()
		in 		
			let _=G.iter_edges_e (fun e-> rtc_helper e) diseq_graph in (local_cache,allvars)
															
	end;;





(*
Local Variables: 
compile-command: "make -C .. bin/sudoku.opt"
End: 
*)

