Starting Reduce... 
Starting Omega...oc
infer_heap_nodes
infer var: [y,b]
new infer var: [inf_ann_32,inf_a_33,inf_b_34,y,b]
infer_heap_nodes
infer var: [inf_ann_32,inf_a_33,inf_b_34,y,b]
new infer var: [inf_ann_36,inf_m_37,inf_ann_32,inf_a_33,inf_b_34,y,b]
Entail  (1): Valid. 
<1>true & b!=null & a=inf_a_33 & m=inf_m_37 & inf_ann_36<=0 & inf_ann_32<=0 & inf_b_34=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_37>@inf_ann_36[Orig][LHSCase]; 
               y::node<inf_a_33,inf_b_34>@inf_ann_32[Orig]]
inferred pure: [inf_ann_36<=0; inf_ann_32<=0; inf_b_34=b]

infer_heap_nodes
infer var: [y,b]
new infer var: [inf_ann_51,inf_a_52,inf_b_53,y,b]
infer_heap_nodes
infer var: [inf_ann_51,inf_a_52,inf_b_53,y,b]
new infer var: [inf_ann_55,inf_m_56,inf_ann_51,inf_a_52,inf_b_53,y,b]
Entail  (2): Valid. 
<1>true & b!=null & a=inf_a_52 & m=inf_m_56 & inf_ann_55<=0 & inf_ann_51<=0 & inf_b_53=b & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_m_56>@inf_ann_55[Orig][LHSCase]; 
               y::node<inf_a_52,inf_b_53>@inf_ann_51[Orig]]
inferred pure: [inf_ann_55<=0; inf_ann_51<=0; inf_b_53=b]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_70,inf_a_71,inf_b_72,y]
infer_heap_nodes
infer var: [inf_ann_70,inf_a_71,inf_b_72,y]
new infer var: [inf_ann_74,inf_m_75,inf_ann_70,inf_a_71,inf_b_72,y]
Entail  (3): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Stop Omega... 140 invocations 
