Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & q=null & n=inf_26 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_26>@M[Orig][LHSCase]]

Entail  (2): Valid. 
<1>true & q=null & n=0 & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Entail  (3): Valid. 
<1>true & q!=null & n=inf_39 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_39>@M[Orig][LHSCase]]

Entail  (4): Fail.(may) cause:15.4 no match for rhs data node: q (may-bug).

Entail  (5): Valid. 
<1>true & n=0 & inf_n_56=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_56>@M[Orig][LHSCase]]
inferred pure: [inf_n_56=0]

Entail  (6): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (7): Valid. 
<1>true & n=0 & inf_n_79=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_79>@M[Orig][LHSCase]]
inferred pure: [inf_n_79=0]

Entail  (8): Valid. 
<1>true & n=0 & inf_n_92=0 & {FLOW,(17,18)=__norm}
inferred heap: [q::ll<inf_n_92>@M[Orig][LHSCase]]
inferred pure: [inf_n_92=0]

Entail  (9): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n=0]

Stop Omega... 112 invocations 
