Starting Reduce... 
Starting Omega...oc

@1! lhs_xpure_orig: flted_8_43+1=n & b=q_45 & (q_45=null & flted_8_43=0 | q_45!=null & 
1<=flted_8_43) & x!=null
@1! lhs_xpure0: flted_8_43+1=n & b=q_45 & 0<=flted_8_43 & x!=null
@1! lhs_rels:None
@1! xp: true
@1! lhs(orig): : true
@1! lhs0(orig): : flted_8_43+1=n & b=q_45 & 0<=flted_8_43 & x!=null
@1! rhs(orig): : 0<a & Anon_44=a
@1! lhs (after filter_ante): : true
@1! fml: : 0<a & Anon_44=a
@1! total_sub_flag:true
@1! vars overlap:[]
@1! quan_var: :[Anon_44]
@1! lhs_xpure: : true
@1! lhs_xpure(w ann): : true
@1! new_p_assume: : false
@1! rhs_xpure: : 0<a & Anon_44=a
@1! fml2: : 1<=a
@1! new_p2: : false
@1! quan_var: :[Anon_44]
@1! iv: :[n,a]
@1! new_p1: : false
@1! new_p2: : false
@1! new_p2 (pairwisecheck): : false
@1!todo.slk:18: 24: >>>>>> infer_pure_m <<<<<<
@1!todo.slk:18: 24: Did not manage to infer a useful precondition
@1!todo.slk:18: 24: LHS : : true
@1!todo.slk:18: 24: RHS : : 0<a & Anon_44=a
@1!todo.slk:18: 24: new pure: : false
infer_pure_m@1
infer_pure_m@1 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (1): Fail.(may) cause:(failure_code=213)  true |-  Anon_44=a;  true |-  0<a (may-bug).


Stop Omega... 26 invocations 
