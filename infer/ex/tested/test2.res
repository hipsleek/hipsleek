Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true & q=null & n=inf_n_27 & inf_ann_26<=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_27>@inf_ann_26[Orig][LHSCase]]
inferred pure: [inf_ann_26<=0]

Entail  (2): Valid. 

<1>true & q=null & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (3): Valid. 

<1>true & q!=null & n=inf_n_42 & inf_ann_41<=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_42>@inf_ann_41[Orig][LHSCase]]
inferred pure: [inf_ann_41<=0]

Entail  (4): Fail.(may) cause:15.4 no match for rhs data node: q (may-bug).


Entail  (5): Valid. 

<1>true & n=0 & inf_ann_60<=0 & inf_n_61<=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_61>@inf_ann_60[Orig][LHSCase]]
inferred pure: [inf_n_61<=0; inf_ann_60<=0]

Entail  (6): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (7): Valid. 

<1>true & n=0 & inf_ann_85<=0 & n=inf_n_86 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_86>@inf_ann_85[Orig][LHSCase]]
inferred pure: [n=inf_n_86; inf_ann_85<=0]

Entail  (8): Valid. 

<1>true & n=0 & inf_ann_99<=0 & n=inf_n_100 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_100>@inf_ann_99[Orig][LHSCase]]
inferred pure: [n=inf_n_100; inf_ann_99<=0]

Entail  (9): Valid. 

<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Stop Omega... 162 invocations 
