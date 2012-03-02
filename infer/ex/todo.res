Starting Reduce... 
Starting Omega...oc
Entail  (1): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).

<1>true & true & {FLOW,(1,2)=__Error}

Entail  (2): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).


Entail  (3): Valid. 

<1>true & b!=null & a=inf_a_53 & m=inf_m_57 & inf_ann_56<=0 & inf_ann_52<=0 & b=inf_b_54 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_53,inf_b_54>@inf_ann_52[Orig]; 
               b::ll<inf_m_57>@inf_ann_56[Orig][LHSCase]]
inferred pure: [b=inf_b_54; inf_ann_52<=0; inf_ann_56<=0]

Entail  (4): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [b=null]

Entail  (5): Valid. 

<1>true & c=i & 1<=i & {FLOW,(17,18)=__norm}
inferred pure: [1<=i]

Entail  (6): Valid. 

<1>EXISTS(flted_7_93: b::ll<flted_7_93>@M[Orig] & flted_7_93+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0 | x!=null]

Stop Omega... 104 invocations 
