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

 <1>(exists flted_7_67: b::ll<flted_7_67>@M&n=flted_7_67+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (5) : Valid. 

 <1>(exists flted_7_86: b::ll<flted_7_86>@M&n=flted_7_86+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


!!! dumping for sleek_dump(fail)
Entail (6) : Fail.


Entail (7) : Valid. 

 <1>(exists flted_7_139,q_155,flted_7_153: q_155::ll<flted_7_153>@M&flted_7_139=flted_7_153+1 & n=flted_7_139+1 & n=2&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=2; n!=0; n!=1]


Entail (8) : Valid. 

 <1>(exists q_186,flted_7_184: q_186::ll<flted_7_184>@M&n=flted_7_184+1 & 0<n & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1]


Entail (9) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [1>n]


!!! dumping for sleek_dump(fail)
Entail (10) : Fail.


Entail (11) : Valid. 

 <1>emp&a=inf_a_209 & inf_q_210=q & b=inf_b_212 & c=inf_c_213 & inf_ann_211=@M & inf_ann_208=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_q_210::node<inf_b_212,inf_c_213>@inf_ann_211; 
                 x::node<inf_a_209,inf_q_210>@inf_ann_208]
 inferred pure: [inf_ann_208=@M; inf_ann_211=@M]

Stop Omega... 120 invocations 
SAT Count   : 100
SAT % Hit   : 63.%
IMPLY Count : 72
IMPLY % Hit : 56.94%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.124377,263)
Total verification time: 0.13 second(s)
	Time spent in main process: 0.09 second(s)
	Time spent in child processes: 0.04 second(s)

