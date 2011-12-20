Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & q_39=null & 0+1=n & m=inf_47 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_47>@M[Orig][LHSCase]]

Entail  (2): Valid. 
<1>EXISTS(flted_22_64: z::node<flted_22_64>@M[Orig] & q_66=null & flted_22_64=null & 0+1=n & m=inf_74 & {FLOW,(17,18)=__norm})
inferred heap: [y::ll<inf_74>@M[Orig][LHSCase]]

Entail  (3): Valid. 
<1>true & a=y & inf_flted_25_84=null & {FLOW,(17,18)=__norm}
inferred heap: [a::lseg<inf_flted_25_84>@M[Orig][LHSCase]]
inferred pure: [a=y; inf_flted_25_84=null]

Entail  (4): Valid. 
<1>true & a=y & n=inf_95 & {FLOW,(17,18)=__norm}
inferred heap: [a::ll<inf_95>@M[Orig][LHSCase]]
inferred pure: [a=y]

Entail  (5): Fail.(may) cause:(failure_code=213)  z!=null & x!=null |-  x=z (may-bug).

Stop Omega... 151 invocations 
