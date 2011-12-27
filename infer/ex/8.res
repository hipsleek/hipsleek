Starting Reduce... 
Starting Omega...oc
infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_44,inf_flted_8_45,y]
infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_48,inf_m_49,y]
Entail  (1): Valid. 
<1>true & q_39=null & 0+1=n & m=inf_m_49 & inf_ann_48<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_m_49>@inf_ann_48[Orig][LHSCase]]
inferred pure: [inf_ann_48<=0]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_73,inf_flted_8_74,y]
infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_77,inf_m_78,y]
Entail  (2): Valid. 
<1>EXISTS(flted_22_66: z::node<flted_22_66>@M[Orig] & q_68=null & flted_22_66=null & 0+1=n & m=inf_m_78 & inf_ann_77<=0 & {FLOW,(17,18)=__norm})
inferred heap: [y::ll<inf_m_78>@inf_ann_77[Orig][LHSCase]]
inferred pure: [inf_ann_77<=0]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_88,inf_flted_25_89,y]
Entail  (3): Valid. 
<1>true & a=y & inf_ann_88<=0 & inf_flted_25_89=null & {FLOW,(17,18)=__norm}
inferred heap: [a::lseg<inf_flted_25_89>@inf_ann_88[Orig][LHSCase]]
inferred pure: [inf_ann_88<=0; y=a; inf_flted_25_89=null]

infer_heap_nodes
infer var: [y]
new infer var: [inf_ann_100,inf_n_101,y]
Entail  (4): Valid. 
<1>true & a=y & n=inf_n_101 & inf_ann_100<=0 & {FLOW,(17,18)=__norm}
inferred heap: [a::ll<inf_n_101>@inf_ann_100[Orig][LHSCase]]
inferred pure: [inf_ann_100<=0; y=a]

infer_heap_nodes
infer var: [z,y]
new infer var: [inf_ann_120,inf_p_121,z,y]
infer_heap_nodes
infer var: [z,y]
new infer var: [inf_ann_127,inf_flted_31_128,z,y]
Entail  (5): Fail.(may) cause:(failure_code=213)  z!=null & x!=null |-  x=z (may-bug).

Stop Omega... 222 invocations 
