Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>x::node<p,q>@v[Orig]&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (2): Valid. 

<1>true&a=p & b=q&{FLOW,(17,18)=__norm}


@1! lhs_xpure_orig: a=p & b=q & x!=null
@1! lhs_xpure0: a=p & b=q & x!=null
@1! lhs_rels:None
@1! xp: true
@1! lhs(orig): : true
@1! lhs0(orig): : a=p & b=q & x!=null
@1! rhs(orig): : v<:@M
@1! lhs (after filter_ante): : true
@1! fml: : v<:@M
@1! total_sub_flag:false
@1! vars overlap:[]
@1! quan_var: :[]
@1! lhs_xpure: : true
@1! lhs_xpure(w ann): : 0<=v & v<=2
@1! new_p_assume: : 3<=v | v<=0
@1! rhs_xpure: : v<:@M
@1! fml2: : v<=0
@1! new_p2: : v<=0
@1! quan_var: :[]
@1! iv: :[v]
@1! new_p1: : 3<=v | v<=0
@1! new_p2: : v<=0
@1! new_p2 (pairwisecheck): : v<=0
infer_pure_m@1
infer_pure_m@1 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=0),0)
Entail  (3): Valid. 

<1>true&a=p & b=q & v<=0&{FLOW,(17,18)=__norm}
inferred pure: [v<=0]


@2! lhs_xpure_orig: a=p & b=q & x!=null
@2! lhs_xpure0: a=p & b=q & x!=null
@2! lhs_rels:None
@2! xp: true
@2! lhs(orig): : true
@2! lhs0(orig): : a=p & b=q & x!=null
@2! rhs(orig): : v<:@I
@2! lhs (after filter_ante): : true
@2! fml: : v<:@I
@2! total_sub_flag:false
@2! vars overlap:[]
@2! quan_var: :[]
@2! lhs_xpure: : true
@2! lhs_xpure(w ann): : 0<=v & v<=2
@2! new_p_assume: : 3<=v | v<=1
@2! rhs_xpure: : v<:@I
@2! fml2: : v<=1
@2! new_p2: : v<=1
@2! quan_var: :[]
@2! iv: :[v]
@2! new_p1: : 3<=v | v<=1
@2! new_p2: : v<=1
@2! new_p2 (pairwisecheck): : v<=1
infer_pure_m@2
infer_pure_m@2 EXIT out :(new es,inf pure,rel_ass) :(None,Some( v<=1),0)
Entail  (4): Valid. 

<1>true&a=p & b=q & v<=1&{FLOW,(17,18)=__norm}
inferred pure: [v<=1]

Stop Omega... 31 invocations 
