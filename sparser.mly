%{
  (* Parser for a more expressive language *)

  open Globals
  open Iast
  open Sleekcommons

  module F = Iformula
  module P = Ipure

  type type_decl =
	| Data of data_decl
	| Enum of enum_decl
	| View of view_decl

  type decl =
  | Type of type_decl
  | Proc of proc_decl
  | Coercion of coercion_decl

  type member =
	| Field of (typed_ident * loc)
	| Inv of F.formula
	| Method of proc_decl

  type spec_qualifier =
	| Static
	| Dynamic

  type ann =
	| AnnMode of mode
	| AnnType of typ

  let get_pos x = 
	{ start_pos = Parsing.symbol_start_pos ();
	  end_pos = Parsing. symbol_end_pos ();
	  mid_pos = Parsing.rhs_start_pos x;
	}	

  let rec get_mode (anns : ann list) : mode = match anns with
	| ann :: rest -> begin
		match ann with
		  | AnnMode m -> m
		  | _ -> get_mode rest
	  end
	| [] -> ModeOut (* default to ModeOut if there is no annotation. *)

  let rec get_modes (anns : ann list list) : mode list =
	match anns with
	  | alist :: rest ->
		  let m_rest = get_modes rest in
		  let m = get_mode alist in
			m :: m_rest
	| [] -> []


  let expand_exp_list mk l r pos =
    let b, oe = l in
	  match oe with
		| Some e ->
			let tmp = P.build_relation mk e r pos in
			let res = P.mkAnd b tmp pos in
			  (res, Some r)
		| None -> report_error pos ("parse error in lhs of relational operator")

  let rec split_members mbrs = match mbrs with
	| mbr :: rest -> begin
		let fields, invs, meths = split_members rest in
		  match mbr with
			| Field f -> (f :: fields, invs, meths)
			| Inv i -> (fields, i :: invs, meths)
			| Method m ->
				(fields, invs, m :: meths)
	  end
	| [] -> ([], [], [])

%}

%token AND
%token ANDAND
%token ASSERT
%token ASSUME
%token AT
%token BIND
%token BOOL
%token BREAK
%token BY
%token CASE
%token CBRACE
%token CHECKENTAIL
%token CHECKENTAILPURE 
%token CAPTURERESIDUE
%token CLASS
%token COERCION
%token COLON
%token COLONCOLON
%token COMMA
%token COMPOSE
%token CONSEQ
%token CONST
%token CONTINUE
%token CPAREN
%token CSQUARE
%token DATA
%token DDEBUG
%token DTIME
%token DIFF
%token DISTR
%token DIV
%token DOLLAR
%token DOT
%token DOUBLEQUOTE
%token DERIVE
%token DYNAMIC
%token ELSE
%token ENSURES
%token ENUM
%token EOF
%token EQ
%token EQEQ
%token EQUIV
%token EXISTS
%token EXTENDS
%token FALSE
%token FLOAT
%token FORALL
%token GT
%token GTE
%token HASH
%token <string> IDENTIFIER
%token IF
%token IMPLIES
%token IMPLY
%token IMPORT
%token IN
%token <string> JAVA
%token LEFTARROW
%token LEMMA
%token LEMMAS
%token LET
%token <float> LITERAL_FLOAT
%token <int> LITERAL_INTEGER
%token NOTIN
%token BAGMAX
%token BAGMIN
%token FOLD
%token INT
%token INTERR
%token INTERSECT
%token INV
%token LT
%token LTE
%token MAX
%token MINUS
%token MIN
%token NEQ
%token NEW
%token NOT
%token NULL
%token OBRACE
%token OFF
%token OPAREN
%token ON
%token OP_ADD_ASSIGN
%token OP_DEC
%token OP_DIV_ASSIGN
%token OP_INC
%token OP_MOD_ASSIGN
%token OP_MULT_ASSIGN
%token OP_SUB_ASSIGN
%token OR
%token OROR
%token ORWORD
%token OSQUARE
%token PERCENT
%token PLUS
%token PRED
%token PRIME
%token PRINT
%token REF
%token REQUIRES
%token <string> RES
%token RETURN
%token RIGHTARROW
%token <string> SELF
%token SEMICOLON
%token SPLIT
%token STAR
%token STATIC
%token SUBSET
%token THEN
%token <string> THIS
%token TO
%token TRUE
%token VIEW
%token VOID
%token UNFOLD
%token UNION
%token WHERE
%token WHILE
%token <string> FLOW

%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE

/*%nonassoc LOWER_THAN_SEMICOLON*/
%left SEMICOLON
%left OR
%left AND
%right NOT
%left EQ NEQ GT GTE LT LTE
%left PLUS MINUS
%left STAR
%left UMINUS


%nonassoc LOWER_THAN_DOT_OP
%nonassoc OP_DEC OP_INC
%left DOT

%start program,data_decl,view_decl,coercion_decl,formulas,command,opt_command_list
%type <Iast.prog_decl> program
%type <Iast.data_decl> data_decl
%type <Iast.view_decl> view_decl
%type <Iast.coercion_decl> coercion_decl
%type <Iformula.struc_formula*bool> formulas
%type <Sleekcommons.command> command
%type <Sleekcommons.command list> opt_command_list
%%

opt_command_list
	: {[]}
	| command_list {List.rev $1}
;

command_list
  : non_empty_command { [$1] }
  | command_list non_empty_command { $2 :: $1 }
;

command
  :non_empty_command{$1}
  | { EmptyCmd }
;
non_empty_command
  : data_decl {
    DataDef $1
  }
  | view_decl {
	  PredDef $1
	}
  | coercion_decl {
	  LemmaDef $1
	}
  | let_decl {
	  $1
	}
  | checkentail_cmd {
	  EntailCheck $1
	}
  | captureresidue_cmd {
	  CaptureResidue $1
	}
  | print_cmd {
	  PrintCmd $1
	}
  | time_cmd {
    $1
  }
  | pure_pred_decl{
    PurePredDef $1
  }
  | check_pure_entail{
   (* EntailCheckPure $1*)
    CheckEntailPure $1
  }
  |pure_lemmas_def{
    (*lemma for recursive user-defined pure predicates*)
    PureLemmaDef $1
  }
;



program : {
  { prog_data_decls = [];
  prog_global_var_decls = [];
	prog_enum_decls = [];
	prog_view_decls = [];
	prog_proc_decls = [];
  prog_coercion_decls = [];

  (*added Oct 16 2010*)
  prog_pure_pred_decl = [];
  prog_pure_lemma = []; }
}
;

data_decl
  : data_header data_body DOT{
	  { data_name = $1;
		data_fields = $2;
		data_parent_name = "Object";
		data_invs = []; (* F.mkTrue (get_pos 1); *)
		data_methods = [] }
	}
;

data_header
  : DATA IDENTIFIER { $2 }
;

data_body
  : OBRACE opt_field_list CBRACE { $2 }
;

opt_field_list
  : { [] }
  | field_list opt_semicolon { List.rev $1 }
;

opt_semicolon
  : {}
  | SEMICOLON {}
;

field_list
  : typ IDENTIFIER { [(($1, $2), get_pos 1)] }
  | field_list SEMICOLON typ IDENTIFIER {
			if List.mem $4 (List.map (fun f -> snd (fst f)) $1) then
				report_error (get_pos 4) ($4 ^ " is duplicated")
			else
				(($3, $4), get_pos 3) :: $1
		}
;

/*this part is for recursive user-defined predicate Oct 14 2010*/

pure_pred_decl :
  pure_header EQEQ pure_body inv_for_user_define DOT {
  {$1 with pure_inv = $4; pure_formula = $3}
 }
;

inv_for_user_define:
  INV inv_for_user_define_res{
          $2        
}
  | {[]}
;

inv_for_user_define_res:
  pure_relation AND inv_for_user_define_res {
    $1::$3
  }
  | pure_relation{
    [$1]
  }
  | {[]}
;

pure_header :
  PRED IDENTIFIER OPAREN opt_ann_cid_list CPAREN
  /*because I am so lazy so I want to reuse opt_and_cid_list for this reason, I
  do not care about ann, branch, etc*/
  {
    let cids, _ = List.split $4 in
    let cids, _ = List.split cids in
    let cids = List.map fst cids in

    let rec init_argument id_list = 
        match id_list with
        |head::tail -> (head, INIT)::(init_argument tail)
        |[] -> [] in

    let argument_list_for_pure_predicate = init_argument cids in
    {
      predicate_name = $2;
      pure_vars = argument_list_for_pure_predicate ;
      pure_inv = [];
      pure_formula = []
    }
  
  }
;

pure_body:
  one_case ORWORD pure_body{
          Case_in_rec($1)::($3)
  }
  | one_case{
          [Case_in_rec ($1)]
  }
;

one_case: 
  OPAREN EXISTS opt_ann_cid_list COLON one_case_part CPAREN {
    let cids, _ = List.split $3 in
    let cids, _ = List.split cids in
    let cids = List.map fst cids in
    {
      forall_list = [];
      exists_list = cids;
      formula_element = $5;
    } 
  }
  | one_case_part {
    {
      forall_list = [];
      exists_list = [];
      formula_element = $1;
    }
  }
;

one_case_part:
  pure_relation {
    [$1]
  }
  | pure_relation AND one_case_part {
    $1::$3 
  }
;

pure_relation:
        /*I have to add this because bconstr only accepts a list of expression*/
  | cexp EQ cexp {
    Pure (P.mkEq $1 $3 (get_pos 2))
  }
  | cexp LT cexp{
    Pure(P.mkLt $1 $3 (get_pos 2))
  }
  | cexp LTE cexp{
    Pure(P.mkLte $1 $3 (get_pos 2))
  }
  | cexp GT cexp{
    Pure(P.mkGt $1 $3 (get_pos 2))
  }
  | cexp GTE cexp{
    Pure(P.mkGte $1 $3 (get_pos 2))
  }
  | IDENTIFIER OPAREN cexp_list CPAREN{
    PreFormula (
    {
      pred_name = $1;
      argument_list = $3 
    }
   ) 
  }
;

/********** Views **********/

view_decl
  : view_header EQEQ view_body opt_inv DOT{
	{ $1 with 
    view_formula = (fst $3); 
    view_invariant = $4; 
    try_case_inference = (snd $3) }
  }
  | view_header EQ error {
	  report_error (get_pos 2) ("use == to define a view")
	}
;

opt_inv
  : { (P.mkTrue no_pos, []) }
  | INV pure_constr opt_branches { ($2, $3) }
;
opt_branches
  : { [] }
  | AND OSQUARE branches CSQUARE { $3 }
;

branches
  : branch {[$1]}
  | branch SEMICOLON branches { $1 :: $3 }

opt_branch
  : { "" }
  | DOUBLEQUOTE IDENTIFIER DOUBLEQUOTE COLON { $2 }

branch
  : DOUBLEQUOTE IDENTIFIER DOUBLEQUOTE COLON pure_constr { ($2, $5) }
 ;


view_header
  : PRED IDENTIFIER LT opt_ann_cid_list GT {
	let cids, anns = List.split $4 in
    let cids, br_labels = List.split cids in
	  if List.exists 
		(fun x -> match snd x with | Primed -> true | Unprimed -> false) cids 
	  then
		report_error (get_pos 1) 
		  ("variables in view header are not allowed to be primed")
	  else
		let modes = get_modes anns in
		  { view_name = $2;
			view_data_name = "";
			view_vars = List.map fst cids;
            view_labels = br_labels;
			view_modes = modes;
			view_typed_vars = [];
			view_formula = F.mkETrue top_flow (get_pos 1);
			view_invariant = (P.mkTrue (get_pos 1), []);
			try_case_inference = false
			}
  }
  ;

cid
  : IDENTIFIER { ($1, Unprimed) }
  | IDENTIFIER PRIME { ($1, Primed) }
  | RES { (res, Unprimed) }
  | SELF { (self, Unprimed) }
  | THIS { (this, Unprimed) }
;

view_body
  : formulas { ((F.subst_stub_flow_struc top_flow (fst $1)),(snd $1)) }
;

/********** Constraints **********/

/*
opt_heap_arg_list
  : { [] }
  | heap_arg_list { List.rev $1 }
;
*/

heap_arg_list
  : heap_arg_list_aux { List.rev $1 }
;

heap_arg_list_aux
  : heap_arg { [$1] }
  | heap_arg_list_aux COMMA heap_arg { $3 :: $1}
;

heap_arg
  : cexp { $1 (* including variables. to be resolved later *) }
;

opt_heap_arg_list2
  : { [] }
  | heap_arg_list2 { List.rev $1 }
;

heap_arg_list2
	: heap_arg2 { [$1] }
	| heap_arg_list2 COMMA heap_arg2 {
			if List.mem (fst $3) (List.map fst $1) then
				report_error (get_pos 3) ((fst $3) ^ " is duplicated")
			else
				$3 :: $1
		}
;

heap_arg2
	: IDENTIFIER EQ cexp { ($1, $3) }
;

opt_cid_list
  : {
	[] : (ident * primed) list
  }
  | cid_list {
	  List.rev $1 : (ident * primed) list
	}
;

cid_list
  : cid {
	([$1]) : (ident * primed) list
  }
  | cid_list COMMA cid {
	  if List.mem (fst $3) (List.map fst $1) then
		report_error (get_pos 3) ("identifier " ^ (fst $3) ^ " is duplicated")
	  else
		($3 :: $1) : (ident * primed) list
	}
;


/* annotated cid list */
opt_ann_cid_list
  : { [] }
  | ann_cid_list {
	  List.rev $1
	}

ann_cid_list
  : ann_cid {
	[$1]
  }
  | ann_cid_list COMMA ann_cid {
	  $3 :: $1
	}
;

ann_cid 
  : opt_branch cid opt_ann_list {
	(($2, $1), $3)
  }
;

opt_ann_list
  : {
	[]
  }
  | ann_list {
	  List.rev $1
	}
;

ann_list
  : ann {
	[$1]
  }
  | ann_list ann {
	  $2 :: $1
	}
;

ann
  : AT IN {
	AnnMode ModeIn
  }
  | AT IDENTIFIER {
	if $2 = "out" then AnnMode ModeOut
	else report_error (get_pos 2) ("unrecognized mode: " ^ $2)
  }
;
sq_clist
	:OSQUARE opt_cid_list CSQUARE {$2}
;

formulas 
	: extended_constr{($1,false)}
	| disjunctive_constr {((Iformula.formula_to_struc_formula $1),true)}
	;


extended_constr
	: r_constr {[$1]}
	| extended_constr ORWORD r_constr {$3::$1}
	;
	
r_constr_opt
	: {[]}	
	| r_constr {[$1]}
	| OSQUARE extended_constr CSQUARE {$2}
	;
	
impl_list
	: pure_constr LEFTARROW extended_constr SEMICOLON 
		{
			let _ = if(List.length (Ipure.look_for_anonymous_pure_formula $1))>0 then 
				report_error (get_pos 1) ("anonimous variables in case guard are disalowed")
				else true in 
			[($1,$3)]}
	| impl_list pure_constr LEFTARROW extended_constr SEMICOLON {(($2,$4)::$1)}
;

r_constr 
	: CASE OBRACE impl_list CBRACE 
	{
		Iformula.ECase 
			{
				Iformula.formula_case_branches = $3;
				Iformula.formula_case_pos = (get_pos 3) 
			}
	}
	| sq_clist one_constr r_constr_opt
	{Iformula.EBase 
						{
						 	Iformula.formula_ext_explicit_inst = $1;
						 	Iformula.formula_ext_implicit_inst = [];
							Iformula.formula_ext_exists = [];
						 	Iformula.formula_ext_base = $2;				
						 	Iformula.formula_ext_continuation = $3;
						 	Iformula.formula_ext_pos = (get_pos 2);
							} 
		} 
;



disjunctive_constr
  : one_constr { (* each case of a view definition *)
	$1
  }
  | disjunctive_constr ORWORD one_constr {
	  F.mkOr $1 $3 (get_pos 2)
	}
  | error {
	  report_error (get_pos 1) ("parse error in constraints")
	}
;
one_constr
	: core_constr { $1 }
	|  OPAREN EXISTS opt_cid_list COLON core_constr CPAREN {
	  match $5 with
		| F.Base ({F.formula_base_heap = h;
				   F.formula_base_pure = p;
				   F.formula_base_flow = fl;
                   F.formula_base_branches = b}) ->
			F.mkExists $3 h p fl b (get_pos 1)
		| _ -> report_error (get_pos 4) ("only Base is expected here.")
	}
;


core_constr
  : heap_constr flows_and_branches { F.replace_branches (snd $2) (F.formula_of_heap_with_flow $1 (fst $2) (get_pos 1)) }
  | pure_constr flows_and_branches { F.replace_branches (snd $2) (F.formula_of_pure_with_flow $1 (fst $2) (get_pos 1)) }
  | heap_constr AND pure_constr flows_and_branches { F.mkBase $1 $3 (fst $4) (snd $4) (get_pos 2) }
;

flows_and_branches
	: flow_constraints opt_branches { ($1,$2)}
	| opt_branches {(stub_flow,$1)}

flow_constraints :
	AND FLOW IDENTIFIER {$3} 
	
	
opt_formula_label : 
        AT DOUBLEQUOTE IDENTIFIER DOUBLEQUOTE {(fresh_branch_point_id $3)}
        |{(fresh_branch_point_id "")}

heap_constr
  : simple_heap_constr { $1 }
  | heap_constr STAR simple_heap_constr { F.mkStar $1 $3 (get_pos 2) }
;

simple_heap_constr
  : cid COLONCOLON IDENTIFIER LT heap_arg_list GT opt_formula_label{
	let h = F.HeapNode { F.h_formula_heap_node = $1;
						 F.h_formula_heap_name = $3;
						 F.h_formula_heap_full = false;
						 F.h_formula_heap_with_inv = false;
						 F.h_formula_heap_pseudo_data = false;
						 F.h_formula_heap_arguments = $5;
						 F.h_formula_heap_label = $7;
						 F.h_formula_heap_pos = get_pos 2 } in
	  h
  }
  | cid COLONCOLON IDENTIFIER LT opt_heap_arg_list2 GT opt_formula_label{
	  let h = F.HeapNode2 { F.h_formula_heap2_node = $1;
							F.h_formula_heap2_name = $3;
							F.h_formula_heap2_full = false;
							F.h_formula_heap2_with_inv = false;
							F.h_formula_heap2_pseudo_data = false;
							F.h_formula_heap2_arguments = $5;
							F.h_formula_heap2_label = $7;
							F.h_formula_heap2_pos = get_pos 2 } in
		h
	}
;

pure_constr
  : simple_pure_constr opt_formula_label 
  { 
    match $1 with 
    | P.BForm (b,_) -> P.BForm (b,$2)
    | P.And _ -> $1
    | P.Or  (b1,b2,_,l) -> P.Or(b1,b2,$2,l)
    | P.Not (b1,_,l) -> P.Not(b1,$2,l)
    | P.Forall (q,b1,_,l)-> P.Forall(q,b1,$2,l)
    | P.Exists (q,b1,_,l)-> P.Exists(q,b1,$2,l)
  }
  | pure_constr AND simple_pure_constr { P.mkAnd $1 $3 (get_pos 2) }
;

disjunctive_pure_constr
  : pure_constr OR pure_constr { P.mkOr $1 $3 None (get_pos 2) }
  | disjunctive_pure_constr OR pure_constr { P.mkOr $1 $3 None (get_pos 2) }
;

simple_pure_constr
  : lbconstr {
	fst $1
  }
  | OPAREN disjunctive_pure_constr CPAREN {
	  $2
	}
  | EXISTS OPAREN opt_cid_list COLON pure_constr CPAREN {
	  let qf f v = P.mkExists [v] f None (get_pos 1) in
	  let res = List.fold_left qf $5 $3 in
		res
	}
  | FORALL OPAREN opt_cid_list COLON pure_constr CPAREN {
	  let qf f v = P.mkForall [v] f None (get_pos 1) in
	  let res = List.fold_left qf $5 $3 in
		res
	}
  | TRUE {
	  P.mkTrue (get_pos 1)
	}
  | FALSE {
	  P.mkFalse (get_pos 1)
	}
  | cid {
	  P.BForm (P.mkBVar $1 (get_pos 1), None )
	}
  | NOT cid {
	  P.mkNot (P.BForm (P.mkBVar $2 (get_pos 2), None )) None (get_pos 1)
	}
  /*this maybe the place to modify for my purpose Oct 4 2010*/
;

lbconstr
  : bconstr {
    (fst $1, snd $1)
  }
  | lbconstr NEQ cexp_list {
	  expand_exp_list P.mkNeq $1 $3 (get_pos 2)
	}
  | lbconstr EQ cexp_list {
	  expand_exp_list P.mkEq $1 $3 (get_pos 2)
	}
  | lbconstr LT cexp_list {
	  expand_exp_list P.mkLt $1 $3 (get_pos 2)
	}
  | lbconstr LTE cexp_list {
	  expand_exp_list P.mkLte $1 $3 (get_pos 2)
	}
  | lbconstr GT cexp_list {
	  expand_exp_list P.mkGt $1 $3 (get_pos 2)
	}
  | lbconstr GTE cexp_list {
	  expand_exp_list P.mkGte $1 $3 (get_pos 2)
	}
;

bconstr
  : cexp_list LT cexp_list {
    let p = P.build_relation P.mkLt $1 $3 (get_pos 2) in
    let _ = print_string("test print: "^Iprinter.string_of_pure_formula p^"\n") in
	  (p, Some $3)
  }
  | cexp_list LTE cexp_list {
	  let p = P.build_relation P.mkLte $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list GT cexp_list {
	  let p = P.build_relation P.mkGt $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list GTE cexp_list {
	  let p = P.build_relation P.mkGte $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list EQ cexp_list {
	  let p = P.build_relation P.mkEq $1 $3 (get_pos 2) in
		(p, Some $3)
	}
  | cexp_list NEQ cexp_list {
	  let p = P.build_relation P.mkNeq $1 $3 (get_pos 2) in
		(p, Some $3)
	}
	/* bag_constr */
  | cid IN cexp {
	  (P.BForm (P.BagIn ($1, $3, get_pos 2), None), None)
	}
  | cid NOTIN cexp {
	  (P.BForm (P.BagNotIn ($1, $3, get_pos 2), None), None)
	}
  | cexp SUBSET cexp {
	  (P.BForm (P.BagSub ($1, $3, get_pos 2), None), None)
	}
  | BAGMAX OPAREN cid COMMA cid CPAREN {
	  (P.BForm (P.BagMax ($3, $5, get_pos 2), None), None)
	}
  | BAGMIN OPAREN cid COMMA cid CPAREN {
	  (P.BForm (P.BagMin ($3, $5, get_pos 2), None), None)
	}
  /*must add some thing to handle user-defined predicate Oct 20 2010*/
;

/* constraint expressions */

cexp
  : cid {
		P.Var ($1, get_pos 1)
  }
  | LITERAL_INTEGER {
	  P.IConst ($1, get_pos 1)
	}
  | LITERAL_INTEGER cid {
	  P.mkMult (P.IConst ($1, get_pos 1)) (P.Var ($2, get_pos 2)) (get_pos 1)
	}
  | cexp STAR cexp {
      P.mkMult $1 $3 (get_pos 2)
  }
  | cexp PLUS cexp {
	  P.mkAdd $1 $3 (get_pos 2)
	}
  | cexp MINUS cexp {
	  P.mkSubtract $1 $3 (get_pos 2)
	}
  |cexp STAR cexp{
    P.mkMult $1 $3 (get_pos 2)
  }
  | MINUS cexp %prec UMINUS {
	  P.mkSubtract (P.IConst (0, get_pos 1)) $2 (get_pos 1)
	}
  | MAX OPAREN cexp COMMA cexp CPAREN {
	  P.mkMax $3 $5 (get_pos 1)
	}
  | MIN OPAREN cexp COMMA cexp CPAREN {
	  P.mkMin $3 $5 (get_pos 1)
	}
  | NULL {
	  P.Null (get_pos 1)
	}
	/* bags */
  | OBRACE opt_cexp_list CBRACE {
	  P.Bag ($2, get_pos 1)
	}
  | UNION OPAREN opt_cexp_list CPAREN {
	  P.BagUnion ($3, get_pos 1)
	}
  | INTERSECT OPAREN opt_cexp_list CPAREN {
	  P.BagIntersect ($3, get_pos 1)
	}
  | DIFF OPAREN cexp COMMA cexp CPAREN {
	  P.BagDiff ($3, $5, get_pos 1)
	}

;

opt_cexp_list
  : { [] }
  | cexp_list { $1 }
;

cexp_list
  : cexp_list_rec {
	List.rev $1
  }
;

cexp_list_rec
  : cexp {
	[$1]
  }
  | cexp_list_rec COMMA cexp {
	  $3 :: $1
	}
;

/********** Procedures and Coercion **********/


checkentail_cmd
  : CHECKENTAIL meta_constr DERIVE extended_meta_constr DOT{
	($2, $4)
  }
;

captureresidue_cmd
  : CAPTURERESIDUE DOLLAR IDENTIFIER DOT{
	($3)
  }
;

compose_cmd
  : COMPOSE OSQUARE id_list CSQUARE OPAREN meta_constr SEMICOLON meta_constr CPAREN {
	($3, $6, $8)
  }
  | COMPOSE OPAREN meta_constr SEMICOLON meta_constr CPAREN {
	  ([], $3, $5)
	}
;

print_cmd
  : PRINT IDENTIFIER DOT{
		PCmd $2
  }
  | PRINT DOLLAR IDENTIFIER DOT{
	  PVar $3
	}
;

time_cmd 
  : DTIME ON IDENTIFIER {Time(true, $3, get_pos 1)}
  | DTIME OFF IDENTIFIER {Time(false, $3, get_pos 1)}

let_decl
  : LET DOLLAR IDENTIFIER EQ meta_constr DOT{
	LetDef ($3, $5)
  }
;

extended_meta_constr
  : DOLLAR IDENTIFIER {
	MetaVar $2
  }
  | formulas {
	  MetaEForm (F.subst_stub_flow_struc n_flow (fst $1))
	}
  | compose_cmd {
	  MetaCompose $1
	}
;

meta_constr
  : DOLLAR IDENTIFIER {
    MetaVar $2
  }
  | disjunctive_constr {
	  MetaForm (F.subst_stub_flow n_flow $1)
	}
  | compose_cmd {
	  MetaCompose $1
	}
;

coercion_decl
  : LEMMA opt_name disjunctive_constr coercion_direction disjunctive_constr DOT{
	{ coercion_type = $4;
	  coercion_name = $2;
	  coercion_head = (F.subst_stub_flow top_flow $3);
	  coercion_body = (F.subst_stub_flow top_flow $5);
	  coercion_proof = Return ({ exp_return_val = None;
								 exp_return_path_id = None ;
								 exp_return_pos = get_pos 1 })
	}
  }
;

coercion_direction
  : LEFTARROW { Left }
  | EQUIV { Equiv }
  | RIGHTARROW { Right }
;

opt_name
  : { "" }
  | DOUBLEQUOTE IDENTIFIER DOUBLEQUOTE { $2 }
;

typ
  : non_array_type { $1 }
  | array_type { $1 }
;

non_array_type
  : INT { int_type }
  | FLOAT { float_type }
  | BOOL { bool_type }
  | IDENTIFIER { Named $1 }
;

array_type
  : array_type rank_specifier { Array (int_type, None) }
  | non_array_type rank_specifier { Array (int_type, None) }
;

rank_specifier
  : OSQUARE comma_list_opt CSQUARE {}
;

comma_list_opt
  : {}
  | comma_list {}
;

comma_list
  : COMMA {}
  | comma_list COMMA {}
;

id_list
  : IDENTIFIER { [$1] }
  | id_list COMMA IDENTIFIER { $3 :: $1 }
;

/*all the the following is added in Oct 21th 2010*/
check_pure_entail
  : CHECKENTAILPURE core_pureentail DOT {
          $2
  }
;

pure_lemmas_def
  :LEMMAS core_pureentail DOT{
     $2
  }
;

core_pureentail:
  OPAREN EXISTS opt_ann_cid_list COLON core_pure CPAREN{
    let cids, _ = List.split $3 in
    let cids, _ = List.split cids in
    let cids = List.map fst cids in
    {
      foralllist = [] ;
      existslist = cids;
      left_hand_side = fst $5;
      right_hand_side = snd $5;
    }    
  }
  | OPAREN FORALL  opt_ann_cid_list COLON core_pure CPAREN{
    let cids, _ = List.split $3 in
    let cids, _ = List.split cids in
    let cids = List.map fst cids in
    {
      foralllist = cids;
      existslist = [];
      left_hand_side = fst $5;
      right_hand_side = snd $5;
    }
  }
  | OPAREN core_pure CPAREN {
    {
      foralllist = [];
      existslist = [];
      left_hand_side = fst $2;
      right_hand_side = snd $2;
    }
  }
  | core_pure {
    {
      foralllist = [];
      existslist = [];
      left_hand_side = fst $1;
      right_hand_side = snd $1;
    }
  }
;

core_pure 
  : one_side DERIVE one_side{
    ($1, $3)
  }
;

one_side
  : | OPAREN core_one_side CPAREN {
    $2    
  }
  | core_one_side {
    $1  
  }
;

core_one_side
  : core_one ORWORD core_one_side {
          (Case_in_rec {
                  forall_list = []; 
                  exists_list = [];
                  formula_element = $1;})::$3
  }
  | core_one {
    [(Case_in_rec {
            forall_list = [];
            exists_list = [];
            formula_element = $1;})]
  }
;

core_one 
  : pure_relation {
    [$1]
  }
  | pure_relation AND core_one {
    $1::$3

  }
;
 
%%
