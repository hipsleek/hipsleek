Starting Omega...oc

@1! view:y::cell<a>@M[HeapNode1]
gather_type_info_heap@1
gather_type_info_heap inp1 :y::cell<a>@M[HeapNode1]
gather_type_info_heap inp2 :
gather_type_info_heap res2 :; (a int); (y cell)
gather_type_info_heap@1 EXIT out :()

@2! view:y::cell<b>@v[HeapNode1]
gather_type_info_heap@2
gather_type_info_heap inp1 :y::cell<b>@v[HeapNode1]
gather_type_info_heap inp2 :; (a int); (y cell); (Anon_full_perm float)
gather_type_info_heap res2 :; (a int); (v AnnT); (b int); (y cell); (Anon_full_perm float)
gather_type_info_heap@2 EXIT out :()

@3!:0: 0: do_match: using  y::cell<a>@M[Orig] to prove  y::cell<b>@v[Orig]
@3!:0: 0: do_match: source LHS:  es_formula: emp&true&{FLOW,(19,20)=__norm}[]
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
@3!:0: 0: do_match: source RHS:  emp&true&{FLOW,(19,20)=__norm}[]
@3! ann_lhs:Some( v=@M)
@3! ann_rhs:None
@3! new_l_args:[#]
@3! new_r_args:[#]
@3! new_l_holes:[0]
@3! new_r_holes:[0]
@3! rem_l_node: emp
@3! rem_r_node: emp
@3! new_l_args:[a]
@3! new_r_args:[b]
@3! l_param_ann:[@M]
@3! r_param_ann:[@v]
@3! imm_n:@v
@3! new_consumed: y::cell<a>@M[Orig]
@3! new_ante: emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]
@3!:0: 0: do_match (after): LHS:  emp&v=@M & a=b&{FLOW,(19,20)=__norm}[]

@3!:0: 0: do_match (after): RHS: emp&true&{FLOW,(19,20)=__norm}[]
@3!:0: 0: heap_entail_split_rhs: 
                            
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
do_match@3
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
do_match@3 EXIT out : 
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


Entail (1) : Fail.

Stop Omega... 2 invocations 
SAT Count   : 1
SAT % Hit   : 0.%
IMPLY Count : 1
IMPLY % Hit : 0.%
Time(cache overhead) : 0. (seconds)

Total verification time: 0.06 second(s)
	Time spent in main process: 0.05 second(s)
	Time spent in child processes: 0.01 second(s)

