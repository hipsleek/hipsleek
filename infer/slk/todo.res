Starting Omega...oc

Entail (1) : Fail.(must) cause: true |-  n=2 & n=1. LOCS:[0;13] (RHS: contradiction)


Entail (2) : Fail.(may) cause: true |-  y!=null. LOCS:[0] (may-bug)


Entail (3) : Valid. 

 <1>emp&b!=null & a=inf_a_61 & m=inf_m_65 & inf_ann_64<=0 & inf_ann_60<=0 & b=inf_b_62&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_65>@inf_ann_64[Orig][LHSCase]; 
                y::node<inf_a_61,inf_b_62>@inf_ann_60[Orig]]
 inferred pure: [b=inf_b_62; inf_ann_60<=0; inf_ann_64<=0]


Entail (4) : Fail.(may) cause: true |-  y!=null. LOCS:[0] (may-bug)


Entail (5) : Valid. 

 <1>emp&c=i & 1<=i&{FLOW,(19,20)=__norm}[]
 inferred pure: [1<=i]


Entail (6) : Valid. 

 <1>EXISTS(flted_7_105: b::ll<flted_7_105>@M[Orig]&flted_7_105+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0 | x!=null]

Stop Omega... 80 invocations 
