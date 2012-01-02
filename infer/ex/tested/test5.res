Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (2): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

infer_heap_nodes
infer var: [x,y]
new infer var: [inf_ann_68,inf_Anon_69,inf_b_70,x,y]
infer_heap_nodes
infer var: [inf_ann_68,inf_Anon_69,inf_b_70,x,y]
new infer var: [inf_ann_72,inf_Anon_73,inf_flted_19_74,inf_ann_68,inf_Anon_69,inf_b_70,x,y]
Entail  (3): Fail.(may) cause:(failure_code=213)  true |-  inf_b_70=b (may-bug).

infer_heap_nodes
infer var: [x,y,b]
new infer var: [inf_ann_115,inf_Anon_116,inf_b_117,x,y,b]
infer_heap_nodes
infer var: [inf_ann_115,inf_Anon_116,inf_b_117,x,y,b]
new infer var: [inf_ann_119,inf_Anon_120,inf_flted_29_121,inf_ann_115,inf_Anon_116,inf_b_117,x,y,b]
Entail  (4): Valid. 
<1>true & Anon_18=1 & Anon_17=inf_Anon_116 & Anon_19=inf_Anon_120 & inf_ann_119<=0 & inf_ann_115<=0 & inf_b_117=b & inf_flted_29_121=null & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_Anon_120,inf_flted_29_121>@inf_ann_119[Orig]; 
               x::node<inf_Anon_116,inf_b_117>@inf_ann_115[Orig]]
inferred pure: [inf_ann_119<=0; inf_ann_115<=0; inf_b_117=b & 
               inf_flted_29_121=null]


ERROR: at _0_0 
Message: y is not found in both sides
 exception in Entail  (5) check
: no residue 
Stop Omega... 125 invocations 
