Starting Omega...oc

Entail (1) : Valid. 

 <1>false&false&{FLOW,(17,18)=__norm}[]
 inferred pure: [n!=0]


Entail (2) : Valid. 

 <1>false&false&{FLOW,(17,18)=__norm}[]
 inferred pure: [x!=null]


Entail (3) : Valid. 

 <1>false&false&{FLOW,(17,18)=__norm}[]
 inferred pure: [x!=null]


Entail (4) : Valid. 

 <1>EXISTS(flted_7_64: b::ll<flted_7_64>@M[Orig]&flted_7_64+1=n&{FLOW,(17,18)=__norm})[]
 inferred pure: [x!=null]


Entail (5) : Fail.(may) cause: q_89=null & flted_7_87=0 | q_89!=null & 1<=flted_7_87 |-  q_89=null. LOCS:[7;6;1;33] (may-bug)

 

Entail (6) : Valid. 

 <1>EXISTS(q_117,flted_7_115: q_117::ll<flted_7_115>@M[Orig]&flted_7_115+1=n & n=1&{FLOW,(17,18)=__norm})[]
 inferred pure: [n=1; n!=0]


Entail (7) : Valid. 

 <1>EXISTS(q_146,flted_7_144: q_146::ll<flted_7_144>@M[Orig]&flted_7_144+1=n & 0<n & n=1&{FLOW,(17,18)=__norm})[]
 inferred pure: [n=1]


Entail (8) : Valid. 

 <1>false&false&{FLOW,(17,18)=__norm}[]
 inferred pure: [n<=0]


Entail (9) : Fail.(must) cause: 0<n & (x=null & n=0 | x!=null & 1<=n) |-  x=null. LOCS:[6;1;49] (must-bug)

 <1>x::ll<n>@M[Orig][LHSCase]&0<n&{FLOW,(1,2)=__Error}[]


Entail (10) : Valid. 

 <1>true&a=inf_a_169 & q=inf_q_170 & b=inf_b_172 & c=inf_c_173 & inf_ann_171<=0 & inf_ann_168<=0&{FLOW,(17,18)=__norm}[]
 inferred heap: [inf_q_170::node<inf_b_172,inf_c_173>@inf_ann_171[Orig]; 
                x::node<inf_a_169,inf_q_170>@inf_ann_168[Orig]]
 inferred pure: [inf_ann_168<=0; inf_ann_171<=0]

Stop Omega... 94 invocations 
