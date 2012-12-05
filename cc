Starting Omega...oc

process_action@1
process_action inp1 :0
process_action inp2 : NothingToDo: No duplicated nodes!
process_action inp3 : es_formula: y::cell<a>@M[Orig]&true&{FLOW,(19,20)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_gen_impl_vars: [v; b]
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: true
process_action inp4 : y::cell<b>@v[Orig]&v=@L&{FLOW,(19,20)=__norm}[]
process_action inp5 : emp&true&{FLOW,(1,22)=__flow}[]
process_action inp6 : emp&true&{FLOW,(1,22)=__flow}[]
process_action@1 EXIT out :
ctx length:0 
 Context: failctx
         fe_kind: MAY
         fe_name: separation entailment
         fe_locs: {
                   fc_message: No duplicated nodes!
                   fc_current_lhs_flow: {FLOW,(19,20)=__norm}}

@4!:0: 0: do_match: using  y::cell<a>@M[Orig] to prove  y::cell<b>@v[Orig]
@4!:0: 0: do_match: source LHS:  es_formula: emp&true&{FLOW,(19,20)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_gen_impl_vars: [v; b]
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: false
@4!:0: 0: do_match: source RHS:  emp&true&{FLOW,(19,20)=__norm}[]
subtype_ann_gen@5@4@3@2
subtype_ann_gen inp1 :[v,b]
subtype_ann_gen inp2 :?
subtype_ann_gen inp3 :?
subtype_ann_gen@5 EXIT out :(true,Some( v=@M),None)

@4! ann_lhs:Some( v=@M)
@4! ann_rhs:None
@4! Imm annotation mismatch:false
@4! new_l_args:[#]
@4! new_r_args:[#]
@4! new_l_holes:[0]
@4! new_r_holes:[0]
@4! rem_l_node: emp
@4! rem_r_node: emp
@4! new_l_args:[a]
@4! new_r_args:[b]
@4! l_param_ann:[@M]
@4! r_param_ann:[@v]
@4! to_rhs: true
@4! to_lhs: v=@M & a=b
@4! imm_n:@v
@4! new_consumed: y::cell<a>@M[Orig]
@4! new_ante: emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]
@4!:0: 0: do_match (after): LHS:  emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]

@4!:0: 0: do_match (after): RHS: emp&true&{FLOW,(19,20)=__norm}[]
@4!:0: 0: heap_entail_split_rhs: 
                            
ante:
 es_formula: emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: y::cell<a>@M[Orig]
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: false
conseq:
 emp&true&{FLOW,(19,20)=__norm}[]
do_match@4@3@2
do_match inp1 : y::cell<a>@M[Orig]
do_match inp2 : y::cell<b>@v[Orig]
do_match inp3 : es_formula: emp&true&{FLOW,(19,20)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_gen_impl_vars: [v; b]
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: false
do_match inp4 : emp&true&{FLOW,(19,20)=__norm}[]
do_match inp5 :[]
do_match@4 EXIT out : 
Good Context: [es_formula: emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]
               es_pure: true
               es_orig_ante: None
               es_heap: y::cell<a>@M[Orig]
               es_aux_conseq: true
               es_must_error: None
               es_var_measures: None
               es_term_err: None
               es_var_zero_perm: 
               es_unsat_flag: false]


process_action@3@2
process_action inp1 :14
process_action inp2 : 
  LHS: y::cell<a>@M[Orig]
  RHS: y::cell<b>@v[Orig]=>Match
process_action inp3 : es_formula: y::cell<a>@M[Orig]&true&{FLOW,(19,20)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_gen_impl_vars: [v; b]
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: false
process_action inp4 : y::cell<b>@v[Orig]&true&{FLOW,(19,20)=__norm}[]
process_action inp5 : y::cell<a>@M[Orig]&true&{FLOW,(19,20)=__norm}[]
process_action inp6 : y::cell<b>@v[Orig]&true&{FLOW,(19,20)=__norm}[]
process_action@3 EXIT out :
ctx length:1 
 Context: [
  emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]
  ]

process_action@2
process_action inp1 :1
process_action inp2 : =>SEARCH:[
  Prio:1
         LHS: y::cell<a>@M[Orig]
         RHS: y::cell<b>@v[Orig]=>Match
  ]
process_action inp3 : es_formula: y::cell<a>@M[Orig]&true&{FLOW,(19,20)=__norm}[]
 es_pure: true
 es_orig_ante: None
 es_heap: emp
 es_gen_impl_vars: [v; b]
 es_aux_conseq: true
 es_must_error: None
 es_var_measures: None
 es_term_err: None
 es_var_zero_perm: 
 es_unsat_flag: false
process_action inp4 : y::cell<b>@v[Orig]&true&{FLOW,(19,20)=__norm}[]
process_action inp5 : y::cell<a>@M[Orig]&true&{FLOW,(19,20)=__norm}[]
process_action inp6 : y::cell<b>@v[Orig]&true&{FLOW,(19,20)=__norm}[]
process_action@2 EXIT out :
ctx length:1 
 Context: [
  emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]
  ]

Entail (1) : Fail.(must) cause: v=@M |-  v=@L. LOCS:[0;6] (must-bug)

Stop Omega... 4 invocations 
SAT Count   : 4
SAT % Hit   : 25.%
IMPLY Count : 1
IMPLY % Hit : 0.%
Time(cache overhead) : 0. (seconds)

Total verification time: 0.06 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.01 second(s)

