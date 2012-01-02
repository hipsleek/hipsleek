Starting Reduce... 
Starting Omega...oc
infer_heap_nodes
infer var: [q]
new infer var: [inf_ann_26,inf_n_27,q]
Entail  (1): Valid. 
<1>true & q=null & n=inf_n_27 & inf_ann_26<=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_27>@inf_ann_26[Orig][LHSCase]]
inferred pure: [inf_ann_26<=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_34,inf_n_35,n]
Entail  (2): Valid. 
<1>true & q=null & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

infer_heap_nodes
infer var: [q]
new infer var: [inf_ann_41,inf_n_42,q]
Entail  (3): Valid. 
<1>true & q!=null & n=inf_n_42 & inf_ann_41<=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_42>@inf_ann_41[Orig][LHSCase]]
inferred pure: [inf_ann_41<=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_49,inf_n_50,n]
Entail  (4): Fail.(may) cause:15.4 no match for rhs data node: q (may-bug).

infer_heap_nodes
infer var: [q]
new infer var: [inf_ann_60,inf_n_61,q]
Entail  (5): Valid. 
<1>true & n=0 & inf_ann_60<=0 & inf_n_61=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_61>@inf_ann_60[Orig][LHSCase]]
inferred pure: [inf_ann_60<=0; inf_n_61=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_74,inf_n_75,n]
Entail  (6): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

infer_heap_nodes
infer var: [n,q]
new infer var: [inf_ann_85,inf_n_86,n,q]
Entail  (7): Valid. 
<1>true & n=0 & inf_ann_85<=0 & inf_n_86=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_86>@inf_ann_85[Orig][LHSCase]]
inferred pure: [inf_ann_85<=0; inf_n_86=0]

infer_heap_nodes
infer var: [q,n]
new infer var: [inf_ann_99,inf_n_100,q,n]
Entail  (8): Valid. 
<1>true & n=0 & inf_ann_99<=0 & inf_n_100=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_100>@inf_ann_99[Orig][LHSCase]]
inferred pure: [inf_ann_99<=0; inf_n_100=0]

infer_heap_nodes
infer var: [n]
new infer var: [inf_ann_113,inf_n_114,n]
Entail  (9): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Stop Omega... 158 invocations 
