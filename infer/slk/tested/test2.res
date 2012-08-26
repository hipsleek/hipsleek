Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&q=null & n=inf_n_27 & inf_ann_26<=0&{FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_27>@inf_ann_26[Orig][LHSCase]]
inferred pure: [inf_ann_26<=0]

Entail  (2): Valid. 

<1>true&q=null & n=0&{FLOW,(17,18)=__norm}

Entail  (3): Valid. 

<1>true&q!=null & n=inf_n_42 & inf_ann_41<=0&{FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_42>@inf_ann_41[Orig][LHSCase]]
inferred pure: [inf_ann_41<=0]

Entail  (4): Fail.(may) cause:15.4 no match for rhs data node: q (may-bug).


Entail  (5): Valid. 

<1>true&n=0 & inf_ann_63<=0 & inf_n_64<=0&{FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_64>@inf_ann_63[Orig][LHSCase]]
inferred pure: [inf_n_64<=0; inf_ann_63<=0]

Entail  (6): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (7): Valid. 

<1>true&n=0 & inf_ann_94<=0 & n=inf_n_95&{FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_95>@inf_ann_94[Orig][LHSCase]]
inferred pure: [n=inf_n_95; inf_ann_94<=0]

Entail  (8): Valid. 

<1>true&n=0 & inf_ann_111<=0 & n=inf_n_112&{FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_112>@inf_ann_111[Orig][LHSCase]]
inferred pure: [n=inf_n_112; inf_ann_111<=0]

Entail  (9): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [n=0]

Stop Omega... 135 invocations 
