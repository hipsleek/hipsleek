(* Ocamlgraph RTC program: Find Biconnected component, *)
(* RTC algorithm generating extra constraints for Equality Logic*)
(* Xuan Bach-24/04/2012*)
open Format
open Graph


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
				let _= converse_depth<-num_ver in
						let _= (self)#findBCC graph v1 v2 in bcc

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
		method getBCCGraph graph v1 v2 =
			let bcp = (self)#transform graph v1 v2 in
			if(bcp != []) then 
				begin
					let rem_ver f graph= f (fun v -> let exist=List.mem v bcp in if(exist=false) then G.remove_vertex graph v) graph in                                                   
         			let _= rem_ver Dfs.postfix graph in ()
					end					
			else G.clear graph				
		
		method add_diseq_edgev2 (graph:G.t) e =
				 if ((G.mem_vertex graph (G.E.src e)) &(G.mem_vertex graph (G.E.dst e))) then
				begin
						let _= G.add_edge_e graph e in true 
					end
				else 	false
				
		method add_diseq_edges (eq_graph:G.t)(diseq_graph:G.t)=
			G.iter_edges_e (fun x->G.add_edge_e eq_graph x) diseq_graph

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
	val mutable number_vars=0
	val mutable local_cache = []
	val bcc= new graphFindBCC
	val mutable g_source= Glabel.create ()
(*	val src= MapDFS.empty*)
	
	method make_chordal graph gr_e=
			let cpg=G.copy graph in 
				let dfs f graph_= f (fun v -> let neib= Adj.list_from_vertex graph_ v in
																				let _= List.map (fun x-> List.map (fun k-> if(k!=x) then 
(*																					let _= print_endline ("chord here:" ^k ^ " " ^x) in*)
																					let _ = G.add_edge graph_ k x in 
																					let _=G.add_edge graph k x in 
																					let mem=Glabel.mem_edge gr_e k x in 
																					if(mem=false) then 
																						let _=number_vars<-number_vars+1 and ed_var=Glabel.E.create k (ref (string_of_int number_vars)) x in Glabel.add_edge_e gr_e ed_var ) neib) neib in
																						G.remove_vertex graph_ v   
				) graph_ in 
					let  _ = dfs Dfs.postfix cpg in ()
	
	method get_var v1 v2 graph=
		try let ed=Glabel.find_edge graph v1 v2 in !(Glabel.E.label ed)
		with Not_found-> let _=print_endline ("get_var:NOT FOUND VAR!!!"^v1^" "^v2) in exit(0)
	
	method check_in_local_cache v v1 v2 gr_e=
				let vv1=self#get_var v v1 gr_e and vv2= self#get_var v v2 gr_e and v1v2=self#get_var v1 v2 gr_e in
					let set1=List.mem (vv1,vv2,v1v2) local_cache in
						if(set1=true) then true
							else let set2=List.mem (vv2,vv1,v1v2) local_cache in
								if(set2=true) then true
									else false
	
(*	method get_id gr_e v1 v2=*)
																		
	method generate_constraints graph es gr_e=
		let helper v el= 
							(*add to local cache*)
(*								let _=G.iter_edges_e (fun x-> print_endline ("g src 2:"^(G.E.src x)^(G.E.dst x)^(G.E.label x))) g_source in*)
							let vv1= ref "" and vv2=ref "" and v1v2= ref "" in
								let _= try vv1:= !(Glabel.E.label (Glabel.find_edge gr_e v el.ver1))  
									with Not_found->  begin let _=number_vars<-number_vars+1 and _= vv1 :=(string_of_int number_vars) in let cx1= Glabel.E.create v vv1 el.ver1 in Glabel.add_edge_e gr_e cx1 end
								in	 
								let _= try vv2:= !((Glabel.E.label (Glabel.find_edge gr_e v el.ver2))) 
											with Not_found-> begin let _=number_vars<-number_vars+1 and _= vv2 :=(string_of_int number_vars) in let cx2= Glabel.E.create v vv2 el.ver2 in Glabel.add_edge_e gr_e cx2 end
								in
								let	_= try v1v2:= !((Glabel.E.label (Glabel.find_edge gr_e el.ver1 el.ver2)))
									with Not_found -> begin let _=number_vars<-number_vars+1 and _= v1v2 :=(string_of_int number_vars) in let cx3= Glabel.E.create el.ver1 v1v2 el.ver2 in Glabel.add_edge_e gr_e cx3 end
								in
								let _=try let ed1= Glabel.find_edge g_source  v el.ver1 in 
										Glabel.E.label ed1 := !v1v2
										with Not_found->let source_e1 = Glabel.E.create v v1v2 el.ver1 in
																				let _= Glabel.add_edge_e g_source source_e1 in ()
								in												
								let _=try let ed2= Glabel.find_edge g_source  v el.ver2 in
															Glabel.E.label ed2 := !v1v2
										with Not_found->let source_e2 = Glabel.E.create v v1v2 el.ver2 in 
																				let _= Glabel.add_edge_e g_source source_e2 in ()
								in																								
								let _= local_cache<-[(!vv1,!vv2,!v1v2)]@local_cache in
(*						  		let _= print_endline ("Constraints in cache:---- "^ v^el.ver1 ^" and "^ v^el.ver2 ^" -> "^ el.ver1^el.ver2) in*)
											let e1={ver1=v;ver2=el.ver1} and e2={ver1=v;ver2=el.ver2} in 
(*											let _=print_endline ("edge to expand:"^v^el.ver1) in   *)
(*											 	let _=print_endline ("edge to expand:"^v^el.ver2) in*)
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
								if((self#check_in_local_cache v e.ver1 e.ver2 gr_e)=false) then
									begin
									  let lb1=self#get_var v e.ver1 gr_e and lb2=self#get_var v e.ver2 gr_e in(*get label of e1 and e2=index of e1 e2*)																													
											try let ed_e= Glabel.find_edge g_source e.ver1 e.ver2 in
												let lbe= !(Glabel.E.label ed_e)in(*find source of e*)
																																									
												try let ed_e1=Glabel.find_edge g_source v e.ver1 and ed_e2=Glabel.find_edge g_source v e.ver2 in
										  		let lb_ed_e1= !(Glabel.E.label ed_e1) and lb_ed_e2= !(Glabel.E.label ed_e2) in(*find source of e1 and source of e2*)
													if((lb_ed_e1<>lbe) & (lb_ed_e2<>lbe) &(lb_ed_e1<>lb_ed_e2)) then
		(*											if(lbe<>lb1 & lbe<>lb11 & lbe<>lb2 & lbe<>lb22) then*)
		(*												if(v1v2<>lb_ed_e1 & v1v2<>lb_ed_e2 & v2v1<>lb_ed_e1 & v2v1<>lb_ed_e2) then*)
															begin
(*																let _= print_endline ("1 Source FOUND edge: "^e.ver1^e.ver2^" has source:"^lbe) in*)
																		let (e1,e2)=helper v e in
		(*																	let _=G.iter_edges_e (fun x-> print_endline ("g src 1:"^(G.E.src x)^(G.E.dst x)^(G.E.label x))) g_source in*)
																			let _= loop_gc e1 and _= loop_gc e2  in () 
																end
												with Not_found->
													if(lbe<>lb1 & lbe<>lb2 ) then
															begin
		(*														let _= print_endline ("2 Source FOUND edge: "^e.ver1^e.ver2^" has source:"^lbe) in*)
																		let (e1,e2)=helper v e in
																			let _= loop_gc e1 and _= loop_gc e2  in () 
		(*																	let _=if(es.ver1="6" & es.ver2="4") then exit(0)*)
																end			
											 with Not_found->																															
		(*											let _= print_endline ("Source NOT FOUND edge: "^e.ver1^e.ver2) in*)
																		let (e1,e2)=helper v e in
																			let _= loop_gc e1 and _= loop_gc e2 in () 
									end								
							end						
					 ) neib_e2  

			 in loop_gc es
	
	method print_all graph =
		let _=Glabel.iter_edges_e (fun x->print_endline ("bach"^(Glabel.E.src x)^(Glabel.E.dst x)^" "^(!(Glabel.E.label x)))) graph in let _=exit(0) in () 
	
	method rtc_v2 eq_graph diseq_graph graph_e num_var=
(*		let _=G.iter_edges_e (fun x->print_endline ((G.E.src x)^(G.E.dst x)^" "^(G.E.label x) )) graph_e in let _=exit(0) in*)
		let _= number_vars<-num_var in
		let rtc_helper e= let cpg= G.copy eq_graph in 
												let check_add=bcc#add_diseq_edgev2 cpg e in
													if(check_add=true) then
														let _=bcc#getBCCGraph cpg (G.E.src e) (G.E.dst e) in(*BCC must contain at least 3 vertex*)
															let _= if((G.is_empty cpg)=false) then 
															let _= bcc#add_diseq_edges cpg diseq_graph in 
																let _= (*if((Clt.is_chordal cpg)=false) then*)  self#make_chordal cpg graph_e in
(*																				let _= bcc#print_chordal_graph cpg in*)
																  let ve={ver1=(G.E.src e);ver2=(G.E.dst e)} in
(*																	let _=print_endline ("bcc of:"^(G.E.src e)^(G.E.dst e)) in*)
																	let _= self#generate_constraints cpg ve graph_e in
(*																	let _=G.clear g_source in*)
																(*To do*)
(*																			let _= print_endline "NEXT BCC OF DISEQ EDGE" in*)
															() in ()
		in 		
			let _=G.iter_edges_e (fun e-> rtc_helper e) diseq_graph in (local_cache,graph_e)
															
	end;;





(*
Local Variables: 
compile-command: "make -C .. bin/sudoku.opt"
End: 
*)

