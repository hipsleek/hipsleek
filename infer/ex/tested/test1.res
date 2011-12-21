Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & a=inf_28 & b=inf_29 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_28,inf_29>@M[Orig]]

Entail  (2): Valid. 
<1>true & n=inf_33 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_33>@M[Orig][LHSCase]]

Entail  (3): Valid. 
<1>true & a=inf_40 & b=inf_41 & c=inf_42 & d=inf_43 & {FLOW,(17,18)=__norm}
inferred heap: [b::node<inf_42,inf_43>@M[Orig]; 
               y::node<inf_40,inf_41>@M[Orig]]
inferred pure: [b=inf_41]

Entail  (4): Valid. 
<1>true & a=inf_49 & b=inf_50 & m=inf_51 & {FLOW,(17,18)=__norm}
inferred heap: [b::ll<inf_51>@M[Orig][LHSCase]; 
               y::node<inf_49,inf_50>@M[Orig]]
inferred pure: [b=inf_50]

Entail  (5): Valid. 
<1>true & x=y & n=inf_55 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_55>@M[Orig][LHSCase]]

Entail  (6): Valid. 
<1>true & n=0 & x=y & inf_n_63=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_63>@M[Orig][LHSCase]]
inferred pure: [inf_n_63=0]

Entail  (7): Valid. 
<1>true & x=y & n=inf_72 & {FLOW,(17,18)=__norm}
inferred heap: [x::ll<inf_72>@M[Orig][LHSCase]]

Entail  (8): Valid. 
<1>true & a=ia & b=ib & {FLOW,(17,18)=__norm}

Entail  (9): Valid. 
<1>true & inf_flted_43_91=null & 1<=inf_a_90 & {FLOW,(17,18)=__norm}
inferred heap: [y::node<inf_a_90,inf_flted_43_91>@M[Orig]]
inferred pure: [inf_flted_43_91=null & 1<=inf_a_90]

Entail  (10): Valid. 
<1>EXISTS(flted_47_117: true & flted_47_117=null & 1<=aa & {FLOW,(17,18)=__norm})
inferred pure: [1<=aa]

Entail  (11): Valid. 
<1>true & n=m & {FLOW,(17,18)=__norm}

Entail  (12): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (13): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [y!=null]

Stop Omega... 137 invocations 
