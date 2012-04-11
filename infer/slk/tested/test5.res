Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (2): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (3): Fail.(may) cause:(failure_code=213)  b!=null |-  inf_b_80=b;  true |-  inf_flted_19_84=null (may-bug).


Entail  (4): Valid. 

<1>true&Anon_18=1 & Anon_17=inf_Anon_136 & Anon_19=inf_Anon_140 & inf_ann_139<=0 & inf_ann_135<=0 & b=inf_b_137 & inf_flted_29_141=null&{FLOW,(17,18)=__norm}
inferred heap: [x::node<inf_Anon_136,inf_b_137>@inf_ann_135[Orig]; 
               y::node<inf_Anon_140,inf_flted_29_141>@inf_ann_139[Orig]]
inferred pure: [inf_flted_29_141=null; b=inf_b_137; inf_ann_135<=0; 
               inf_ann_139<=0]


ERROR: at _0_0 
Message: y is not found in both sides
 exception in Entail  (5) check
: no residue 
Stop Omega... 104 invocations 
