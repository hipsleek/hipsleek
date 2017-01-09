Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&a=inf_a_42 & b=inf_b_43 & c=inf_c_45 & d=inf_d_46 & inf_ann_44<:@I & inf_ann_41<:@I&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_b_43::node<inf_c_45,inf_d_46>@inf_ann_44; 
                 y::node<inf_a_42,inf_b_43>@inf_ann_41]
 inferred pure: [inf_ann_41<:@I; inf_ann_44<:@I]


Entail (2) : Valid. 

 <1>emp&a=inf_a_52 & b=inf_b_53 & inf_ann_51=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_a_52,inf_b_53>@inf_ann_51]
 inferred pure: [inf_ann_51=@M]


Entail (3) : Valid. 

 <1>emp&inf_n_58=n & inf_ann_57=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::ll<inf_n_58>@inf_ann_57]
 inferred pure: [inf_ann_57=@M]


!!! dumping for sleek_dump(fail)
Entail (4) : Fail.


!!! dumping for sleek_dump(fail)
Entail (5) : Fail.


Entail (6) : Valid. 

 <1>emp&n=0 & y=null&{FLOW,(19,20)=__norm}[]


Entail (7) : Valid. 

 <1>emp&y=null & n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]


!!! dumping for sleek_dump(fail)
Entail (8) : Fail.


Entail (9) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=1]


Entail (10) : Valid. 

 <1>emp&inf_n_118=n & inf_ann_117=@M & inf_n_118<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::ll<inf_n_118>@inf_ann_117]
 inferred pure: [inf_n_118<=0; inf_ann_117=@M]


Entail (11) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (12) : Valid. 

 <1>(exists q_148,flted_7_146: q_148::ll<flted_7_146>@M&n=flted_7_146+1 & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; n!=0]


Entail (13) : Valid. 

 <1>(exists flted_7_170: b::ll<flted_7_170>@M&n=flted_7_170+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


Entail (14) : Valid. 

 <1>y::ll<n>@M&n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]


Entail (15) : Valid. 

 <1>y::ll<n>@M&y=null&{FLOW,(19,20)=__norm}[]
 inferred pure: [y=null]


Entail (16) : Valid. 

 <1>y::ll<n>@M&y=null&{FLOW,(19,20)=__norm}[]
 inferred pure: [y=null]


!!! dumping for sleek_dump(fail)
Entail (17) : Fail.


Entail (18) : Valid. 

 <1>(exists q_235,flted_7_233: q_235::ll<flted_7_233>@M&n=flted_7_233+1 & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; (n!=0 | y!=null)]


Entail (19) : Valid. 

 <1>(exists q_263,flted_7_261: q_263::ll<flted_7_261>@M&n=flted_7_261+1 & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; n!=0]


Entail (20) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (21) : Valid. 

 <1>(exists flted_7_289: b::ll<flted_7_289>@M&n=flted_7_289+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (22) : Valid. 

 <1>(exists q_314,flted_7_312: q_314::ll<flted_7_312>@M&nn=flted_7_312+1 & nn=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [nn=1; nn!=0]


Entail (23) : Valid. 

 <1>y::ll<n>@M&n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]


Entail (24) : Valid. 

 <1>(exists flted_7_340: b::ll<flted_7_340>@M&n=flted_7_340+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


!!! dumping for sleek_dump(fail)
Entail (25) : Fail.


!!! dumping for sleek_dump(fail)
Entail (26) : Fail.


!!! dumping for sleek_dump(fail)
Entail (27) : Fail.


Entail (28) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [m!=(0-1)]


Entail (29) : Valid. 

 <1>emp&a=inf_a_418 & inf_m_422=m & inf_ann_421=@M & inf_ann_417=@M & b=inf_b_419&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_422>@inf_ann_421; 
                 y::node<inf_a_418,inf_b_419>@inf_ann_417]
 inferred pure: [b=inf_b_419; inf_ann_417=@M; inf_ann_421=@M]


Entail (30) : Valid. 

 <1>emp&b!=null & a=inf_a_437 & inf_m_441=m & inf_ann_440=@M & inf_ann_436=@M & b=inf_b_438&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_441>@inf_ann_440; 
                 y::node<inf_a_437,inf_b_438>@inf_ann_436]
 inferred pure: [b=inf_b_438; inf_ann_436=@M; inf_ann_440=@M]

Stop Omega... 302 invocations 
SAT Count   : 297
SAT % Hit   : 71.38%
IMPLY Count : 258
IMPLY % Hit : 73.64%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.246339,814)
Total verification time: 0.25 second(s)
	Time spent in main process: 0.19 second(s)
	Time spent in child processes: 0.06 second(s)

