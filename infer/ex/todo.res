Starting Reduce... 
Starting Omega...oc
Entail  (1): Fail.(must) cause:(failure_code=213)  true |-  n=2 & n=1 (RHS: contradiction).
<1>true & true & {FLOW,(1,2)=__Error}

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_35,inf_a_36,inf_b_37,y]
infer_heap_nodes
infer var: [inf_ann_35,inf_a_36,inf_b_37,y]
new infer var: [inf_ann_39,inf_m_40,inf_ann_35,inf_a_36,inf_b_37,y]
Entail  (2): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

infer_heap_nodes
infer var: [y,b]
new infer var: [inf_ann_52,inf_a_53,inf_b_54,y,b]
infer_heap_nodes
infer var: [inf_ann_52,inf_a_53,inf_b_54,y,b]
new infer var: [inf_ann_56,inf_m_57,inf_ann_52,inf_a_53,inf_b_54,y,b]
Entail  (3): Valid. 
<1>true & b!=null & a=inf_a_53 & m=inf_m_57 & inf_ann_56<=0 & inf_ann_52<=0 & inf_b_54=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_57>@inf_ann_56[Orig][LHSCase]; 
               y::node<inf_a_53,inf_b_54>@inf_ann_52[Orig]]
inferred pure: [inf_ann_56<=0; inf_ann_52<=0; inf_b_54=b]

infer_heap_nodes
infer var: [b]
new infer var: [inf_ann_71,inf_a_72,inf_b_73,b]
Entail  (4): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [b=null]

Entail  (5): Valid. 
<1>true & c=i & 1<=i & {FLOW,(17,18)=__norm}
inferred pure: [1<=i]

Entail  (6): Valid. 
<1>EXISTS(flted_7_93: b::ll<flted_7_93>@M[Orig] & flted_7_93+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0 | x!=null]

Stop Omega... 107 invocations 
