Starting Reduce... 
Starting Omega...oc

@1! lhs_xpure_orig: 0<a & b=Anon_12 & x!=null
@1! lhs_xpure0: 0<a & b=Anon_12 & x!=null
@1! lhs_rels:None
@1! xp: 0<a
@1! lhs(orig): : 0<a
@1! lhs0(orig): : 0<a & b=Anon_12 & x!=null
@1! rhs(orig): : 0<a & c=a
@1! lhs (after filter_ante): : 0<a
@1! fml: : 0<a & 0<a & c=a
@1! total_sub_flag:false
@1! vars overlap:[]
@1! quan_var: :[c]
@1! lhs_xpure: : 0<a
@1! lhs_xpure(w ann): : 0<a
@1! new_p_assume: : a<=0
@1! rhs_xpure: : 0<a & c=a
@1! fml2: : 1<=a
@1! new_p2: : false
@1! quan_var: :[c]
@1! iv: :[a]
@1! new_p1: : a<=0
@1! new_p2: : false
@1! new_p2 (pairwisecheck): : false
@1!t3.slk:11: 32: >>>>>> infer_pure_m <<<<<<
@1!t3.slk:11: 32: Did not manage to infer a useful precondition
@1!t3.slk:11: 32: LHS : : 0<a
@1!t3.slk:11: 32: RHS : : 0<a & c=a
@1!t3.slk:11: 32: new pure: : false
infer_pure_m@1
infer_pure_m@1 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (1): Fail.(may) cause:(failure_code=213)  0<a |-  c=a (may-bug).



@2! lhs_xpure_orig: b=Anon_13 & x!=null
@2! lhs_xpure0: b=Anon_13 & x!=null
@2! lhs_rels:None
@2! xp: true
@2! lhs(orig): : true
@2! lhs0(orig): : b=Anon_13 & x!=null
@2! rhs(orig): : 0<a & c=a
@2! lhs (after filter_ante): : true
@2! fml: : 0<a & c=a
@2! total_sub_flag:true
@2! vars overlap:[]
@2! quan_var: :[]
@2! lhs_xpure: : true
@2! lhs_xpure(w ann): : true
@2! new_p_assume: : a=c & 1<=c
@2! rhs_xpure: : 0<a & c=a
@2! fml2: : a=c & 1<=c
@2! new_p2: : c=a & 1<=a
@2! quan_var: :[]
@2! iv: :[a,c]
@2! new_p1: : a=c & 1<=c
@2! new_p2: : a=c & 1<=c
@2! new_p2 (pairwisecheck): : c=a & 1<=a
infer_pure_m@2
infer_pure_m@2 EXIT out :(new es,inf pure,rel_ass) :(None,Some( c=a & 1<=a),0)
Entail  (2): Valid. 

<1>true&b=Anon_13 & c=a & 1<=a&{FLOW,(17,18)=__norm}
inferred pure: [1<=a; c=a]


@3! lhs_xpure_orig: 0<a & b=Anon_14 & x!=null
@3! lhs_xpure0: 0<a & b=Anon_14 & x!=null
@3! lhs_rels:None
@3! xp: 0<a
@3! lhs(orig): : 0<a
@3! lhs0(orig): : 0<a & b=Anon_14 & x!=null
@3! rhs(orig): : 0<a & c=a
@3! lhs (after filter_ante): : 0<a
@3! fml: : 0<a & 0<a & c=a
@3! total_sub_flag:true
@3! vars overlap:[a]
@3! quan_var: :[]
@3! lhs_xpure: : 0<a
@3! lhs_xpure(w ann): : 0<a
@3! new_p_assume: : a<=0 | a=c & 1<=c
@3! rhs_xpure: : 0<a & c=a
@3! fml2: : a=c & 1<=c
@3! new_p2: : c=a & 1<=a
@3! quan_var: :[]
@3! iv: :[a,c]
@3! new_p1: : a<=0 | a=c & 1<=c
@3! new_p2: : c=a & 1<=a
@3! new_p2 (pairwisecheck): : a=c & 1<=c
infer_pure_m@3
infer_pure_m@3 EXIT out :(new es,inf pure,rel_ass) :(None,Some( a=c & 1<=c),0)
Entail  (3): Valid. 

<1>true&0<a & b=Anon_14 & a=c & 1<=c&{FLOW,(17,18)=__norm}
inferred pure: [1<=c; a=c]


@4! lhs_xpure_orig: flted_7_87+1=n & b=q_89 & (q_89=null & flted_7_87=0 | q_89!=null & 
1<=flted_7_87) & x!=null
@4! lhs_xpure0: flted_7_87+1=n & b=q_89 & 0<=flted_7_87 & x!=null
@4! lhs_rels:None
@4! xp: true
@4! lhs(orig): : true
@4! lhs0(orig): : flted_7_87+1=n & b=q_89 & 0<=flted_7_87 & x!=null
@4! rhs(orig): : 0<a & Anon_88=a
@4! lhs (after filter_ante): : true
@4! fml: : 0<a & Anon_88=a
@4! total_sub_flag:true
@4! vars overlap:[]
@4! quan_var: :[Anon_88]
@4! lhs_xpure: : true
@4! lhs_xpure(w ann): : true
@4! new_p_assume: : false
@4! rhs_xpure: : 0<a & Anon_88=a
@4! fml2: : 1<=a
@4! new_p2: : false
@4! quan_var: :[Anon_88]
@4! iv: :[n,a]
@4! new_p1: : false
@4! new_p2: : false
@4! new_p2 (pairwisecheck): : false
@4!t3.slk:20: 24: >>>>>> infer_pure_m <<<<<<
@4!t3.slk:20: 24: Did not manage to infer a useful precondition
@4!t3.slk:20: 24: LHS : : true
@4!t3.slk:20: 24: RHS : : 0<a & Anon_88=a
@4!t3.slk:20: 24: new pure: : false
infer_pure_m@4
infer_pure_m@4 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (4): Fail.(may) cause:(failure_code=213)  true |-  Anon_88=a;  true |-  0<a (may-bug).



@5! lhs_xpure_orig: flted_7_116+1=n & 0<a & b=q_118 & (q_118=null & flted_7_116=0 | 
q_118!=null & 1<=flted_7_116) & x!=null
@5! lhs_xpure0: flted_7_116+1=n & 0<a & b=q_118 & 0<=flted_7_116 & x!=null
@5! lhs_rels:None
@5! xp: 0<a
@5! lhs(orig): : 0<a
@5! lhs0(orig): : flted_7_116+1=n & 0<a & b=q_118 & 0<=flted_7_116 & x!=null
@5! rhs(orig): : 0<a & Anon_117=a
@5! lhs (after filter_ante): : 0<a
@5! fml: : 0<a & 0<a & Anon_117=a
@5! total_sub_flag:true
@5! vars overlap:[a]
@5! quan_var: :[Anon_117]
@5! lhs_xpure: : 0<a
@5! lhs_xpure(w ann): : 0<a
@5! new_p_assume: : a<=0
@5! rhs_xpure: : 0<a & Anon_117=a
@5! fml2: : 1<=a
@5! new_p2: : false
@5! quan_var: :[Anon_117]
@5! iv: :[n,a]
@5! new_p1: : a<=0
@5! new_p2: : false
@5! new_p2 (pairwisecheck): : false
@5!t3.slk:23: 30: >>>>>> infer_pure_m <<<<<<
@5!t3.slk:23: 30: Did not manage to infer a useful precondition
@5!t3.slk:23: 30: LHS : : 0<a
@5!t3.slk:23: 30: RHS : : 0<a & Anon_117=a
@5!t3.slk:23: 30: new pure: : false
infer_pure_m@5
infer_pure_m@5 EXIT out :(new es,inf pure,rel_ass) :(None,None,0)
Entail  (5): Fail.(may) cause:(failure_code=213)  0<a |-  Anon_117=a (may-bug).


Stop Omega... 81 invocations 
