#include "xdebug.cppo"
(*
  Proof tracing facilities:

  data types:
  - proof step types:
    + EX left/right (which vars)
    + OR left/right
    + MATCH of what node
    + FOLD of what
    + UNFOLD of what
    + PURE

  - proof:

  functions:
  - start_step (step type) (input antecedent) (input consequent) (proof) -> proof
  - end_step (step type) (outpt antecedent) (output consequent) (proof) -> proof
  - to_xml (proof) -> string

  for now, get the entire proof tree

  selective reporting can be done separately.
*)
open Globals
open VarGen
open GlobProver

module CP = Cpure
module CF = Cformula

(*
  type for proof or disproof.
  one of the leaves of a proof is successful node
  all leaves of a disproof are failures
*)
type proof = 
  | ExLeft of ex_step
  | ExRight of ex_step
  | OrLeft of or_left
  | OrStrucLeft of or_struc_left
  | OrRight of or_right
  | Match of match_step
  | MMatch of mmatch_step (* if one node from the consequent matches multiple nodes from antecedent *)
  | Fold of fold_step
  | Unfold of unfold_step
  | Pure of pure_step
  | CoercionLeft of coercion_step
  | CoercionRight of coercion_step
  | Coercion2 of coercion2_step
  | ContextList of context_list
  | NoAlias
  | UnsatAnte
  | UnsatConseq
  | TrueConseq
  | Failure 
  | PECase of case_step
  | PEBase of base_step
  | PEAssume of assume_step
  | PEEx of eex_step
  | Search of proof list
  | ClassicSepLogic of classic_seplogic_step
  | Unknown
  | CyclicProof of ( CF.formula *  CF.formula)

and ex_step = { ex_step_ante : CF.context;
				ex_step_conseq : CF.formula;
				ex_step_old_vars : CP.spec_var list;
				ex_step_new_vars : CP.spec_var list;
				ex_step_proof : proof }
	
and or_left = { or_left_ante : CF.context;
				or_left_conseq : CF.formula;
				or_left_proofs : proof list (* all proofs here must succeed *) }
	
and or_struc_left = { or_struc_left_ante : CF.context;
					or_struc_left_conseq : CF.struc_formula;
					or_struc_left_proofs : proof list (* all proofs here must succeed *) }

	
and or_right = { or_right_ante : CF.context;
				 or_right_conseq : CF.formula;
				 or_right_proofs : proof list (* at least one must succeed *) }

and match_step = { match_step_ante : CF.context;
				   match_step_conseq : CF.formula;
				   match_step_node : CF.h_formula;
				   match_step_proofs : proof list (* there can be more than one sub proof if coercion occurs. *) }

and mmatch_step = { mmatch_step_ante : CF.context;
					mmatch_step_conseq : CF.formula;
					mmatch_step_node : CF.h_formula;
					mmatch_step_proofs : proof list (* there can be more than one sub proof if coercion occurs. *) }


and fold_step = { fold_step_ante : CF.context;
				  fold_step_conseq : CF.formula;
				  fold_step_var : CP.spec_var;
				  fold_step_fold_proof : proof; (* recursive proof of folding *)
				  fold_step_proofs : proof list (* proofs after fold. There may be more than one of them *) }

and unfold_step = { unfold_step_ante : CF.context;
					unfold_step_conseq : CF.formula;
					unfold_step_node : CF.h_formula;
					unfold_step_proof : proof }

and pure_step = { pure_step_estate : CF.entail_state;
				  pure_step_ante : CP.formula;
				  pure_step_conseq : CP.formula;
				  pure_step_success : bool;
				  pure_step_gist : CP.formula option }
 
and coercion_step = { coercion_step_name : ident;
					  coercion_step_ante : CF.context;
					  coercion_step_conseq : CF.formula;
					  coercion_step_coercion : (CF.formula * CF.formula);
					  coercion_step_proof : proof }

and coercion2_step = { coercion2_step_ante : CF.context;
					   coercion2_step_conseq : CF.formula;
					   coercion2_step_proofs : proof list }

and context_list = { context_list_ante : CF.context list;
					 context_list_conseq : CF.struc_formula;
					 context_list_proofs : proof list }

and case_step = { case_context: CF.context;
				  case_form: CF.struc_formula;
				  case_proofs: proof list}

and base_step = { base_context: CF.context;
				  base_form: CF.struc_formula;
				  base_proof: proof;
				  cont_proof: proof}

and assume_step = { assume_context : CF.context;
					assume_formula : CF.formula}
and eex_step = {eex_context: CF.context;
				eex_formula: CF.struc_formula;
				eex_proof: proof}
					 
and classic_seplogic_step = { classic_seplogic_step_ctx : CF.context;
                              classic_seplogic_step_conseq : CF.formula; }

let mkCoercionLeft ctx conseq clhs crhs prf name = CoercionLeft { coercion_step_name = name;
																  coercion_step_ante = ctx;
																  coercion_step_conseq = conseq;
																  coercion_step_coercion = (clhs, crhs);
																  coercion_step_proof = prf }
  
let mkCoercionRight ctx conseq clhs crhs prf name = CoercionRight { coercion_step_name = name;
																	coercion_step_ante = ctx;
																	coercion_step_conseq = conseq;
																	coercion_step_coercion = (clhs, crhs);
																	coercion_step_proof = prf }

let mkCoercion2 ctx conseq prfs = Coercion2 { coercion2_step_ante = ctx;
											  coercion2_step_conseq = conseq;
											  coercion2_step_proofs = prfs }

let mkOrLeft ctx conseq prfs = OrLeft { or_left_ante = ctx;
										or_left_conseq = conseq;
										or_left_proofs = prfs }
										
let mkOrStrucLeft ctx conseq prfs = OrStrucLeft {   or_struc_left_ante = ctx;
													or_struc_left_conseq = conseq;
													or_struc_left_proofs = prfs }


let mkOrRight ctx conseq prfs = OrRight { or_right_ante = ctx;
										  or_right_conseq = conseq;
										  or_right_proofs = prfs }

let mkExLeft ctx conseq old_vars new_vars prf = ExLeft { ex_step_ante = ctx;
														 ex_step_conseq = conseq;
														 ex_step_old_vars = old_vars;
														 ex_step_new_vars = new_vars;
														 ex_step_proof = prf }

let mkExRight ctx conseq old_vars new_vars prf = ExRight { ex_step_ante = ctx;
														   ex_step_conseq = conseq;
														   ex_step_old_vars = old_vars;
														   ex_step_new_vars = new_vars;
														   ex_step_proof = prf }

let mkPure estate ante conseq success gformula = Pure { pure_step_estate = estate;
														pure_step_ante = ante;
														pure_step_conseq = conseq;
														pure_step_success = success;
														pure_step_gist = gformula }

let mkUnfold ctx conseq node prf = Unfold { unfold_step_ante = ctx;
											unfold_step_conseq = conseq;
											unfold_step_node = node;
											unfold_step_proof = prf }

let mkUnfold_no_conseq ctx node prf = Unfold { unfold_step_ante = ctx;
											unfold_step_conseq = CF.mkTrue_nf no_pos;
											unfold_step_node = node;
											unfold_step_proof = prf }

let mkFold ctx conseq fnode fold_prf prfs = Fold { fold_step_ante = ctx;
												   fold_step_conseq = conseq;
												   fold_step_var = fnode;
												   fold_step_fold_proof = fold_prf;
												   fold_step_proofs = prfs }

let mkMatch ctx conseq mnode prfs = Match { match_step_ante = ctx;
											match_step_conseq = conseq;
											match_step_node = mnode;
											match_step_proofs = prfs }

let mkMMatch ctx conseq mnode prfs = MMatch { mmatch_step_ante = ctx;
											  mmatch_step_conseq = conseq;
											  mmatch_step_node = mnode;
											  mmatch_step_proofs = prfs }
  
let mkContextList cl conseq prfs = ContextList { context_list_ante = cl;
												 context_list_conseq = conseq;
												 context_list_proofs = prfs }

												 
let mkCaseStep cc cf cp = PECase{ case_context=cc;case_form=cf; case_proofs=cp}

let mkBaseStep bc bf bp cp = PEBase{ base_context=bc; base_form=bf; base_proof=bp;  cont_proof= cp}

let mkAssumeStep ac af = PEAssume{ assume_context=ac; assume_formula=af}

let mkEexStep ec ef ep = PEEx{eex_context=ec; eex_formula=ef; eex_proof=ep}

let mkClassicSepLogic ctx conseq = ClassicSepLogic { classic_seplogic_step_ctx = ctx;
                                                     classic_seplogic_step_conseq = conseq; }

let rec string_of_proof prf0 : string =
  let rec to_string buffer prf1 = match prf1 with
	| ExLeft ({ ex_step_ante = ctx;
				ex_step_conseq = conseq;
				ex_step_old_vars = old_vars;
				ex_step_new_vars = new_vars;
				ex_step_proof = prf }) -> begin
		Buffer.add_string buffer "<ExLeft>\n";
		to_string buffer prf;
		Buffer.add_string buffer "</ExLeft>\n"
	  end
	| ExRight ({ ex_step_ante = ctx;
				 ex_step_conseq = conseq;
				 ex_step_old_vars = old_vars;
				 ex_step_new_vars = new_vars;
				 ex_step_proof = prf }) -> begin
		Buffer.add_string buffer "<ExRight>\n";
		to_string buffer prf;
		Buffer.add_string buffer "</ExRight>\n"
	  end
	| OrLeft ({ or_left_ante = ctx;
				or_left_conseq = conseq;
				or_left_proofs = prfs }) -> begin
		Buffer.add_string buffer "<OrLeft>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</OrLeft>\n"
	  end
	| OrStrucLeft ({ or_struc_left_ante = ctx;
				or_struc_left_conseq = conseq;
				or_struc_left_proofs = prfs }) -> begin
		Buffer.add_string buffer "<OrStrucLeft>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</OrStrucLeft>\n"
	  end
	| OrRight ({ or_right_ante = ctx;
				 or_right_conseq = conseq;
				 or_right_proofs = prfs }) -> begin
		Buffer.add_string buffer "<OrRight>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</OrRight>\n";
	  end
	| Match ({ match_step_ante = ctx;
			   match_step_conseq = conseq;
			   match_step_node = mnode;
			   match_step_proofs = prfs }) -> begin
		Buffer.add_string buffer "<Match>\n";
		Buffer.add_string buffer "<Info>\n";
		Buffer.add_string buffer ("<![CDATA[" ^ (Cprinter.string_of_h_formula mnode) ^ "]]>");
		Buffer.add_string buffer "</Info>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</Match>\n";
	  end
	| MMatch ({ mmatch_step_ante = ctx;
				mmatch_step_conseq = conseq;
				mmatch_step_node = mnode;
				mmatch_step_proofs = prfs }) -> begin
		Buffer.add_string buffer "<MMatch>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</MMatch>\n";
	  end
	| Fold ({ fold_step_ante = ctx;
			  fold_step_conseq = conseq;
			  fold_step_var = var;
			  fold_step_fold_proof = fold_prf;
			  fold_step_proofs = prfs }) -> begin
		Buffer.add_string buffer "<Fold>\n";
		Buffer.add_string buffer "<FoldProof>\n";
		to_string buffer fold_prf;
		Buffer.add_string buffer "</FoldProof>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</Fold>\n";
	  end
	| Unfold ({ unfold_step_ante = ctx;
				unfold_step_conseq = conseq;
				unfold_step_node = unode;
				unfold_step_proof = prf }) -> begin
		Buffer.add_string buffer "<Unfold>\n";
		Buffer.add_string buffer ("<Info>" ^ "<![CDATA[" ^ (Cprinter.string_of_h_formula unode) ^ "]]>" ^ "</Info>\n");
		to_string buffer prf;
		Buffer.add_string buffer "</Unfold>\n";
	  end
	| Pure ({ pure_step_ante = ante;
			  pure_step_conseq = conseq;
			  pure_step_success = success;
			  pure_step_gist = gist_f }) -> begin
		Buffer.add_string buffer "<Pure>\n";
		Buffer.add_string buffer (if success then "Success\n" else "Failure\n");
		if Gen.is_some gist_f then begin
		  let gf = Gen.unsome gist_f in
			Buffer.add_string buffer ("<![CDATA[" ^ (Cprinter.string_of_pure_formula gf) ^ "]]>")
		end;
		Buffer.add_string buffer "</Pure>\n";
	  end
	| CoercionLeft ({ coercion_step_name = name;
					  coercion_step_ante = ctx;
					  coercion_step_conseq = conseq;
					  coercion_step_coercion = (clhs, crhs);
					  coercion_step_proof = prf }) -> begin
		Buffer.add_string buffer "<CoercionLeft>\n";
		Buffer.add_string buffer ("<Info>Name: " ^ name ^ "</Info>\n");
		to_string buffer prf;
		Buffer.add_string buffer "</CoercionLeft>\n";
	  end
	| CoercionRight ({ coercion_step_name = name;
					   coercion_step_ante = ctx;
					   coercion_step_conseq = conseq;
					   coercion_step_coercion = (clhs, crhs);
					   coercion_step_proof = prf }) -> begin
		Buffer.add_string buffer "<CoercionRight>\n";
		Buffer.add_string buffer ("<Info>Name: " ^ name ^ "</Info>\n");
		Buffer.add_string buffer ("<Info>Ctx: <![CDATA[" ^ (Cprinter.string_of_context ctx) ^ "]]></Info>\n");
		Buffer.add_string buffer ("<Info>Conseq: <![CDATA[" ^ (Cprinter.string_of_formula conseq) ^ "]]></Info>\n");
		to_string buffer prf;
		Buffer.add_string buffer "</CoercionRight>\n";
	  end
	| Coercion2 ({ coercion2_step_ante = ctx;
				   coercion2_step_conseq = conseq;
				   coercion2_step_proofs = prfs }) -> begin
		Buffer.add_string buffer "<Coercion2>\n";
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</Coercion2>\n";
	  end
	| ContextList ({ context_list_ante = cl;
					 context_list_conseq = conseq;
					 context_list_proofs = prfs }) -> begin
		Buffer.add_string buffer "<ContextList>\n";
		Buffer.add_string buffer ("<Info>CtxList: <![CDATA[" ^ (Cprinter.string_of_context_list cl) ^ "]]></Info>\n");
		Buffer.add_string buffer ("<Info>Conseq: <![CDATA[" ^ (Cprinter.string_of_struc_formula conseq) ^ "]]></Info>\n");
		ignore (List.map (to_string buffer) prfs);
		Buffer.add_string buffer "</ContextList>\n";
	  end
	| NoAlias -> Buffer.add_string buffer "<NoAlias></NoAlias>"
	| UnsatAnte -> Buffer.add_string buffer "<UnsatAnte></UnsatAnte>"
	| UnsatConseq -> Buffer.add_string buffer "<UnsatConseq></UnsatConseq>"
	| TrueConseq -> Buffer.add_string buffer "<TrueConseq></TrueConseq>"
	| Failure -> Buffer.add_string buffer "<Failure></Failure>" 
  | ClassicSepLogic ({ classic_seplogic_step_ctx = ctx;
                       classic_seplogic_step_conseq = conseq; }) ->
      let s = Cprinter.string_of_context ctx in
      Buffer.add_string buffer ("<Classic>\n<Info>" ^ s ^ "</Info>\n</Classic>")
  | CyclicProof (lhs,rhs) ->  let s = (Cprinter.string_of_formula lhs) ^" |- " ^(Cprinter.string_of_formula rhs)in
      Buffer.add_string buffer ("<Classic>\n<Info>" ^ s ^ "</Info>\n</Classic>")
	| _ -> Buffer.add_string buffer "<Failure></Failure>" 
	in
  let buffer = Buffer.create 1024 in
	to_string buffer prf0;
	Buffer.contents buffer

(* log generated proof to a file *)

let proof_file = ref "proof.log"

let log_proof_flag = ref false

let set_proof_file fn = 
  if Sys.file_exists fn then
	failwith ("File " ^ fn ^ " exists!")
  else begin
	log_proof_flag := true;
	proof_file := fn
  end

let log_proof prf =
  if !log_proof_flag then
	let chn = open_out !proof_file in
	let prf_str = string_of_proof prf in
	  output_string chn prf_str;
	  close_out chn
	  
(** An Hoa : Output to HTML **)

(* The resources (i.e. the 4 files hipsleek.css, hipsleek.js, plus.gif, minus.gif) should be put in the same directory as the executable *)
let resources_dir_url = "file://" ^ Gen.get_path Sys.executable_name


let html_output = ref ""

let html_output_file = ref ""

(* Convert a string to HTML: - replace 5 reserved characters <  >  '  ""  &  with entities
                             - replace newline \n with <br> </br>   *)
let convert_to_html s =
	let html_map = [("&","&amp;"); ("<","&lt;"); (">","&gt;"); ("'","&apos;"); ("\"", "&quot;");   ("\n","<br/>\n");] in
	let res = List.fold_left (fun x (y, z) -> Str.global_replace (Str.regexp_string y) z x) s html_map in
		res

let push_proc proc = let unmin_name = Cast.unmingle_name proc.Cast.proc_name in 
	begin
		html_output := !html_output ^ "<li class=\"Collapsed proc\">\n" ^ "Procedure " ^ unmin_name ^ "\n<ul>"; (* ^ "<li class=\"Collapsed procdef\">Internal representation\n<ul>" ^ (convert_to_html (Cprinter.string_of_proc_decl 3 proc)) ^ "</ul></li>" *)
	end

let primitive_procs = ["add___"; "minus___"; "mult___"; "div___"; "eq___"; "neq___"; "lt___"; "lte___"; "gt___"; "gte___"; "land___"; "lor___"; "not___"; "pow___"; "aalloc___"; "is_null___"; "is_not_null___"]

let start_with s p = if (String.length s >= String.length p) then
		String.sub s 0 (String.length p) = p
	else false

let push_list_failesc_context_struct_entailment lctx sf =
	html_output := !html_output ^ "<li class=\"Collapsed context\">Context\n<ul>" ^ (Cprinter.html_of_list_failesc_context lctx) ^ Cprinter.html_vdash ^ (Cprinter.html_of_formula (Cformula.struc_to_precond_formula sf)) 

let push_list_partial_context_formula_entailment lctx sf =
	html_output := !html_output ^ "<li class=\"Collapsed context\">Context\n<ul>" ^ (Cprinter.html_of_list_partial_context lctx) ^ Cprinter.html_vdash ^ (Cprinter.html_of_formula sf) 

(* let push_list_failesc_context ctx =
	html_output := !html_output ^ "<li class=\"Collapsed context\">Context\n<ul>"

let push_list_partial_context ctx =
	html_output := !html_output ^ "<li class=\"Collapsed context\">Context<ul>" ^ *)

let push_pre fce = match fce with
	| Cast.SCall {
		Cast.exp_scall_type = t;
		Cast.exp_scall_method_name = mn;
		Cast.exp_scall_arguments = args;
		Cast.exp_scall_is_rec = ir;
		Cast.exp_scall_path_id = pid;
		Cast.exp_scall_pos = pos } ->
		let unmin_name = Cast.unmingle_name mn in
		if List.mem unmin_name primitive_procs then false
		else begin
			let line_loc = "<a href=\"#L" ^ (line_number_of_pos pos) ^ "\">" ^ "line " ^ (line_number_of_pos pos) ^ "</a>" in
			let message = if (start_with unmin_name "array_get_elm_at___") then
					"Memory safety of array access at line " ^ line_loc
				else if (start_with unmin_name "update___") then
					"Memory safety of array update at line " ^ line_loc
				else "Precondition of procedure call " ^ (convert_to_html (Cprinter.string_of_exp fce)) ^ " at " ^ line_loc ^ " holds" in
			html_output :=  !html_output ^ "<li class=\"Collapsed pre\">\n" ^ message ^ "<ul>";
			true
		end
	| _ -> failwith "push_pre: unexpected expr"
		
let push_assert_assume ae = match ae with
	| Cast.Assert {
		Cast.exp_assert_asserted_formula = fa;
		Cast.exp_assert_assumed_formula = fas;
		Cast.exp_assert_path_id = pid;
    Cast.exp_assert_type = atype;
		Cast.exp_assert_pos = pos } -> let line_loc = "<a href=\"#L" ^ (line_number_of_pos pos) ^ "\">" ^ "line " ^ (line_number_of_pos pos) ^ "</a>" in
    let assert_str = match atype with
      | None -> "Assertion"
      | Some true -> "Assertion_exact"
      | Some false -> "Assertion_inexact" in
		html_output := !html_output ^ "<li class=\"Collapsed assert\">\n" ^ assert_str ^ " at " ^ line_loc ^ " holds\n<ul>"
	| _ -> failwith "push_assert_assume: unexpected expr"

let push_post () = html_output := 
	!html_output ^ "<li class=\"Collapsed post\">\nProcedure post-condition holds\n<ul>"

let push_term () = html_output := 
	!html_output ^ "<li class=\"Collapsed term\">Termination of all procedures\n<ul>"
			
let push_pure_imply ante conseq r = html_output := 
	!html_output ^ "<li class=\"Collapsed pureimply" ^ (if r then "valid" else "invalid") ^ "\">Verification condition\n" ^ "<ul>" ^ (Cprinter.html_of_pure_formula ante) ^ Cprinter.html_vdash ^ (Cprinter.html_of_pure_formula conseq) ^ "\n"

(* prover input | output are all leaves of the proof trees, so we push and pop at the same time *)

let push_pop_prover_input prover_inp prover_name = html_output :=
	!html_output ^ "<li class=\"Collapsed proverinput" ^ "\">Input to prover " ^ prover_name ^ "\n<ul>" ^ (convert_to_html prover_inp) ^ "</ul></li>"
	
let push_pop_prover_output prover_out prover_name = html_output := 
	!html_output ^ "<li class=\"Collapsed proveroutput" ^ "\">Output of prover " ^ prover_name ^ "\n<ul>" ^ (convert_to_html prover_out) ^ "</ul></li>"

let push_term_checking pos reachable =
    let line_loc = "<a href=\"#L" ^ (line_number_of_pos pos) ^ "\">" ^ "line " ^ (line_number_of_pos pos) ^ "</a>" in
    html_output := !html_output ^ "<li class=\"Collapsed term\">Termination checking at " ^ line_loc ^ 
    (if not reachable then "\n<ul>Unreachable recursive call" else "") ^ "\n<ul>"	
(*	
let push_pop_entail_variance (es, f, res) = html_output := 
	!html_output ^ "<li class=\"Collapsed termentail" ^ "\">Well-foundedness checking" ^ "\n<ul>" ^
  (Cprinter.html_of_formula es) ^ Cprinter.html_vdash ^ (Cprinter.html_of_pure_formula f) ^ " : " ^ (if res then "valid" else "failed") ^ "</ul></li>"
*)
let push_entail_variance (es, f) = html_output := 
	!html_output ^ "<li class=\"Collapsed termentail" ^ "\">Well-foundedness checking" ^ "\n<ul>" ^
  (Cprinter.html_of_formula es) ^ Cprinter.html_vdash ^
  (Cprinter.html_of_pure_formula f)

let push_pop_unreachable_variance () = html_output := 
	!html_output ^ "<li class=\"Collapsed termunreach" ^ "\">Unreachable" ^ "</ul></li>" 

let push_pop_entail_variance_res res = html_output := 
	!html_output ^ "<li class=\"Collapsed termres" ^ "\">Variance checking result " ^ "\n<ul>" ^
	(convert_to_html (if res then "Valid" else "Invalid")) ^ "</ul></li>"
	
let pop_div () = html_output := !html_output ^ "</ul></li>\n"

let append_html s =
	let s = convert_to_html s in
		html_output := !html_output ^ s
		
let append_html_no_convert s =	html_output := !html_output ^ s

let html_of_hip_source src =
	let srclines = Str.split (Str.regexp "\n") src in
	let _,srclines = List.fold_right (fun x (y, z) -> if (not y && x = "") then (false,[]) else (true,x :: z)) srclines (false,[]) in (* remove trailing \n *)
	let res, _ = List.fold_left (fun (accumulated,current_line_no) next_line -> 
			let new_accumulated = accumulated ^ 
					"<tr id=\"L" ^ (string_of_int current_line_no) ^ "\" class=\"" ^ (if (current_line_no mod 2 = 0) then "EvenSourceLine" else "OddSourceLine") ^ "\">" ^
						"<td>" ^ (string_of_int current_line_no) ^ "</td>" ^
						"<td><pre>" ^ next_line ^ "</pre></td>" ^
					"</tr>\n" in
			let new_line_no = current_line_no + 1 in
				(new_accumulated,new_line_no)) ("",1) srclines in
		"<table>" ^ res ^ "</table>"
	
(* An Hoa : experiment with JSON storage of proof *)
let jsondecls = ref ""

let jsonproof = ref "var jsonproof = ["

let initialize_html source_file_name = let source = (Gen.SysUti.string_of_file source_file_name) in
	let source_html = html_of_hip_source source in
	begin
	jsonproof := "var srcfilename = " ^ (strquote source_file_name) ^ ";" ^ !jsonproof;
	html_output_file := source_file_name ^ "_proof.html";
	html_output := 
"<html>
<head> 
	<link rel=\"stylesheet\" type=\"text/css\" href=\"" ^ resources_dir_url ^ "hipsleek.css\" />
	<script type=\"text/javascript\" src=\"" ^ resources_dir_url ^ "hipsleek.js\"></script> 
</head>
<body> 
<h1>" ^ source_file_name ^ "</h1>
<ul class=\"TreeView\" id=\"ProofTree\">
<li class=\"Collapsed progsource\">Source<ul>" ^ source_html ^ "</ul></li>";
	end
	
let post_process_html () = 	html_output := !html_output ^ 
"</ul>
<script>
	SetupTreeView(\"ProofTree\");
</script>
</body>
</html>"
		

(* An Hoa : experiment with JSON storage of proof *)

(* start a compound JSON object, a compound object must have a field items which is an array consisting of component objects *)
let start_compound_object () =
	jsonproof := !jsonproof ^ "{ items : ["

let add_proc proc vres =
	let unmin_name = Cast.unmingle_name proc.Cast.proc_name in
		jsonproof := !jsonproof ^ "], type : \"proc\", name : " ^ (strquote unmin_name) ^ ", success : " ^ (strquote (string_of_bool vres)) ^ "},\n"

let primitive_procs = ["add___"; "minus___"; "mult___"; "div___"; "eq___"; "neq___"; "lt___"; "lte___"; "gt___"; "gte___"; "land___"; "lor___"; "not___"; "pow___"; "aalloc___"; "is_null___"; "is_not_null___"]

let start_with s p = if (String.length s >= String.length p) then
		String.sub s 0 (String.length p) = p
	else false

let add_list_failesc_context_struct_entailment lctx sf =
	jsonproof := !jsonproof ^ "], type : \"listfailesc\", context : " ^ (strquote (Cprinter.html_of_list_failesc_context lctx)) ^ ", fml : " ^ (strquote (Cprinter.html_vdash ^ (Cprinter.html_of_formula (Cformula.struc_to_precond_formula sf)))) ^ "},\n"

let add_list_partial_context_formula_entailment lctx sf =
	jsonproof := !jsonproof ^ "], type : \"listfailesc\", context : " ^ (strquote (Cprinter.html_of_list_partial_context lctx)) ^ ", fml : " ^ (strquote (Cprinter.html_vdash ^ (Cprinter.html_of_formula (Cformula.struc_to_precond_formula sf)))) ^ "},\n"

let add_pre fce = match fce with
	| Cast.SCall {
		Cast.exp_scall_type = t;
		Cast.exp_scall_method_name = mn;
		Cast.exp_scall_arguments = args;
		Cast.exp_scall_is_rec = ir;
		Cast.exp_scall_path_id = pid;
		Cast.exp_scall_pos = pos } ->
		let unmin_name = Cast.unmingle_name mn in
		let is_primitive = List.mem unmin_name primitive_procs in
		let lineloc = line_number_of_pos pos in
		let precndtype = if (start_with unmin_name "array_get_elm_at___") then "precnd_arracc" else if (start_with unmin_name "update___") then "precnd_arrupdt" else "precnd" in
			jsonproof :=  !jsonproof ^ "], type : " ^ (strquote precndtype) ^ ", line : " ^ (strquote lineloc) ^ ", is_primitive : " ^ (strquote (string_of_bool is_primitive)) ^ "},\n"
	| _ -> failwith "push_pre: unexpected expr"
		
let add_assert_assume ae = match ae with
	| Cast.Assert {
		Cast.exp_assert_asserted_formula = fa;
		Cast.exp_assert_assumed_formula = fas;
		Cast.exp_assert_path_id = pid;
    Cast.exp_assert_type = atype;
		Cast.exp_assert_pos = pos } -> 
      let lineloc = line_number_of_pos pos in
      let assert_str = match atype with
        | None -> "Assertion"
        | Some true -> "Assertion_exact"
        | Some false -> "Assertion_inexact" in
		jsonproof := !jsonproof ^ "], type : \"" ^ assert_str ^ "\", line : " ^ (strquote lineloc) ^ "},\n"
	| _ -> failwith "push_assert_assume: unexpected expr"

let add_post () = 
	jsonproof := !jsonproof ^ "], type : \"post\"},\n"

(*let push_term () = jsonproof := 
	!jsonproof ^ "<li class=\"Collapsed term\">Termination of all procedures\n<ul>"*)
			
let add_pure_imply ante conseq is_valid prover_name prover_input prover_output = 
	jsonproof := !jsonproof ^ "{ type : \"pureimply\"," ^ (*	prover_input : " ^ (strquote prover_input) ^ ",*) "	prover_output : " ^ (strquote prover_output) ^ ", prover : " ^ (strquote prover_name) ^ ", is_valid : " ^ (strquote (string_of_bool is_valid)) ^ ",	formula : " ^ (strquote ((Cprinter.html_of_pure_formula ante) ^ Cprinter.html_vdash ^ (Cprinter.html_of_pure_formula conseq))) ^ "},\n"

(* End of JSON proof generator *)

let write_html_output () =
	let resource_dir = (Gen.get_path Sys.executable_name) ^ "html_resources/" in
	let template = Gen.SysUti.string_of_file (resource_dir ^ "hipsleek.html") in
	let setup_script = !jsonproof ^ "\n];\n" in
	let htmloutres = Str.global_replace (Str.regexp_string "//$SETUP_SCRIPT") setup_script template in
	let htmloutres = Str.global_replace (Str.regexp_string "$$RESOURCE_DIR_URL$$") ("file://" ^ resource_dir) htmloutres in
	(* let () = print_endline !jsonproof in *)
	let () = post_process_html () in
	let chn = open_out !html_output_file in
	let chntest = open_out "testjason.html" in
		output_string chn !html_output;
		output_string chntest htmloutres;
		close_out chn;
		close_out chntest;;

