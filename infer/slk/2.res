Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=0]


Entail (2) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (3) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (4) : Valid. 

 <1>EXISTS(flted_7_68: b::ll<flted_7_68>@M[Orig]&flted_7_68+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (5) : Fail.(may) cause: q_97=null & flted_7_95=0 | q_97!=null & 1<=flted_7_95 |-  q_97=null. LOCS:[7;6;1;33] (may-bug)


Entail (6) : Valid. 

 <1>EXISTS(q_129,flted_7_127: q_129::ll<flted_7_127>@M[Orig]&flted_7_127+1=n & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; n!=0]


Entail (7) : Valid. 

 <1>EXISTS(q_162,flted_7_160: q_162::ll<flted_7_160>@M[Orig]&flted_7_160+1=n & 0<n & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1]


Entail (8) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n<=0]


Entail (9) : Fail.(must) cause: 0<n & (x=null & n=0 | x!=null & 1<=n) |-  x=null. LOCS:[6;1;50] (must-bug)


Entail (10) : Valid. 

 <1>emp&a=inf_a_187 & q=inf_q_188 & b=inf_b_190 & c=inf_c_191 & inf_ann_189<=0 & inf_ann_186<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_q_188::node<inf_b_190,inf_c_191>@inf_ann_189[Orig]; 
                x::node<inf_a_187,inf_q_188>@inf_ann_186[Orig]]
 inferred pure: [inf_ann_186<=0; inf_ann_189<=0]

Stop Omega... 84 invocations 
