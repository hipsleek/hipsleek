Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (2) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=0]


Entail (3) : Fail.(may) cause:AndR[ b!=null |-  inf_b_80=b. LOCS:[19];  true |-  inf_flted_19_84=null. LOCS:[0;19] (may-bug).]


Entail (4) : Valid. 

 <1>emp&Anon_18=1 & Anon_17=inf_Anon_136 & Anon_19=inf_Anon_140 & inf_ann_139<=0 & inf_ann_135<=0 & b=inf_b_137 & inf_flted_29_141=null&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_Anon_140,inf_flted_29_141>@inf_ann_139[Orig]; 
                x::node<inf_Anon_136,inf_b_137>@inf_ann_135[Orig]]
 inferred pure: [inf_flted_29_141=null; b=inf_b_137; inf_ann_135<=0; 
                inf_ann_139<=0]


ERROR: at _0_0 
Message: y is not found in both sides
 
Entailment Failure (5) Failure("y is not found in both sides")
: no residue 
Stop Omega... 86 invocations 
