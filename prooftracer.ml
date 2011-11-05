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
  | Unknown 

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

let hipsleekjs = "
/*
 Script obtained from http://www.ridgway.co.za/archive/2005/10/30/asimplecssbasedtreeview.aspx
 */

Array.prototype.indexOf = IndexOf;

//Toggles between two classes for an element
function ToggleClass(element, firstClass, secondClass, event)
{
    event.cancelBubble = true;
    
    var classes = element.className.split(\" \");
    var firstClassIndex = classes.indexOf(firstClass);
    var secondClassIndex = classes.indexOf(secondClass);
    
    if (firstClassIndex == -1 && secondClassIndex == -1)
    {
        classes[classes.length] = firstClass;
    }
    else if (firstClassIndex != -1)
    {
        classes[firstClassIndex] = secondClass;
    }
    else
    {
        classes[secondClassIndex] = firstClass;
    }
    
    element.className = classes.join(\" \");
    
}

//Finds the index of an item in an array
function IndexOf(item)
{
    for (var i=0; i < this.length; i++)
    {        
        if (this[i] == item)
        {
            return i;
        }
    }
    
    return -1;
}

//The toggle event handler for each expandable/collapsable node
//- Note that this also exists to prevent any IE memory leaks 
//(due to circular references caused by this)
function ToggleNodeStateHandler(event)
{
    ToggleClass(this, \"Collapsed\", \"Expanded\", (event == null) ? window.event : event);
}

//Prevents the onclick event from bubbling up to parent elements
function PreventBubbleHandler(event)
{
    if (!event) event = window.event;
    event.cancelBubble = true;
}

//Adds the relevant onclick handlers for the nodes in the tree view
function SetupTreeView(elementId)
{
    var tree = document.getElementById(elementId);
    var treeElements = tree.getElementsByTagName(\"li\");
    
    for (var i=0; i < treeElements.length; i++)
    {
        if (treeElements[i].getElementsByTagName(\"ul\").length > 0)
        {
            treeElements[i].onclick = ToggleNodeStateHandler; 
        }
        else
        {
            treeElements[i].onclick = PreventBubbleHandler; 
        }
    }
}"

let hipsleekcss = "
/*
 Style sheet obtained from http://www.ridgway.co.za/archive/2005/10/30/asimplecssbasedtreeview.aspx
 Modified by An Hoa
 */

h1 {
	color : green;
}

.proc {
	border-style : double;
	font-family : Arial;
}

.procdef {
	color:blue;
	font-size : 0.75em;
	font-weight : normal;
	border-style : groove;
	font-family : monospace;
}

.pre {
	background : aliceblue;
	font-weight : normal;
	border-style : solid;
	font-family : Arial;
}

.post {
	background : burlywood;
	font-weight : normal;
	font-family : Arial;
	border-style : ridge;
}

.term {
	font-weight : normal;
	font-family : Arial;
	border-style : double;
}

.proverinput {
	color : black;
	font-size : 0.75em;
	background : goldenrod;
	font-weight : normal;
	font-family : monospace;
	border-style : double.;
}

.proveroutput {
	color : darkmagenta;
	font-size : 0.75em;
	background : greenyellow;
	font-weight : normal;
	font-family : monospace;
	border-style : double;
}

.pureimplyvalid {
	color : green;
	font-weight : normal;
	border-style : dashed;
}

.pureimplyinvalid {
	color : red;
	font-weight : normal;
	border-style : dashed;
}

.TreeView 
{
    font: Verdana;
    line-height: 20px;
	cursor: pointer; 
	font-style: normal;
}

.TreeView li
{
    /* The padding is for the tree view nodes */
    padding: 0 0 0 18px;
    float: left;
    width: 100%;
    list-style: none;
}

.TreeView, .TreeView ul
{
    margin: 0;
    padding: 0;
}

li.Expanded 
{
    background: url(http://www.ridgway.co.za/Images/ridgway_co_za/minus.gif) no-repeat left top;
}

li.Expanded ul
{
	display: block;
}

li.Collapsed 
{
	background: url(http://www.ridgway.co.za/Images/ridgway_co_za/plus.gif) no-repeat left top;
}

li.Collapsed ul
{
    display: none;
}"

let html_output = ref ""

let html_output_file = ref ""

(* Convert a string to HTML: - replace 5 reserved characters <  >  '  ""  &  with entities
                             - replace newline \n with <br> </br>   *)
let convert_to_html s =
	let html_map = [("&","&amp;"); ("<","&lt;"); (">","&gt;"); ("'","&apos;"); ("\"", "&quot;");   ("\n","<br/>\n"); ("\t","&nbsp;&nbsp;&nbsp;&nbsp;")] in
	let res = List.fold_left (fun x (y, z) -> Str.global_replace (Str.regexp_string y) z x) s html_map in
		res

let push_proc proc_name = html_output := 
	!html_output ^ "<li class=\"Collapsed proc\">\n" ^"Procedure " ^ proc_name ^ "<ul>"

let push_procdef pdef = html_output :=
	!html_output ^ "<li class=\"Collapsed procdef\">Internal representation\n<ul>" ^ (convert_to_html pdef) ^ "</ul></li>"

let push_pre s = html_output := 
	!html_output ^ "<li class=\"Collapsed pre\">\n" ^ 
	"Precondition of procedure call " ^ (convert_to_html s) ^ " holds" ^ "<ul>"

let push_post () = html_output := 
	!html_output ^ "<li class=\"Collapsed post\">\nProcedure post-condition holds\n<ul>"

let push_term () = html_output := 
	!html_output ^ "<li class=\"Collapsed term\">Termination of all procedures\n<ul>"

let push_pure_imply r = html_output := !html_output ^ "<li class=\"Collapsed pureimply" ^ (if r then "valid" else "invalid") ^ "\">Verification condition\n" ^ "<ul>"

let push_prover_input () = 	html_output := 
	!html_output ^ "<li class=\"Collapsed proverinput" ^ "\">Input to prover\n<ul>"

let push_prover_output () = html_output := 
	!html_output ^ "<li class=\"Collapsed proveroutput" ^ "\">Output of prover\n<ul>"

let pop_div () = html_output := !html_output ^ "</ul></li>\n"

let pop_li () = html_output := !html_output ^ "</li>\n"
		
let append_html s =
	let s = convert_to_html s in
		html_output := !html_output ^ s
		
let append_html_no_convert s =	html_output := !html_output ^ s

let initialize_html source_file_name = 
	begin
	html_output_file := source_file_name ^ "_proof.html";
	html_output := 
"<html>
<head>" ^ 
"	<style type=\"text/css\">" ^ hipsleekcss ^ "</style>" ^
"	<script type=\"text/javascript\">" ^ hipsleekjs ^ "</script>" ^
(* "<link rel=\"stylesheet\" type=\"text/css\" href=\"hipsleek.css\" />" ^ *)
(* "<script type=\"text/javascript\" src=\"hipsleek.js\"></script>" ^ *)
"</head>
<body>\n" ^ 
"<h1>" ^ source_file_name ^ "</h1>\n" ^
"<ul class=\"TreeView\" id=\"ProofTree\">";
	end
	
let post_process_html () = 	html_output := !html_output ^ 
"</ul>
<script>
	SetupTreeView(\"ProofTree\");
</script>
</body>
</html>"
		
let write_html_output () =
	let _ = post_process_html () in
	let chn = open_out !html_output_file in
		output_string chn !html_output;
		close_out chn;;
