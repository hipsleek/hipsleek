Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (2) : Valid. 

 <1>(exists flted_7_52: b::ll<flted_7_52>@M&n=flted_7_52+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (3) : Valid. 

 <1>emp&b!=null & a=inf_a_65 & inf_m_69=m & inf_ann_68=@M & inf_ann_64=@M & b=inf_b_66&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_69>@inf_ann_68; 
                 y::node<inf_a_65,inf_b_66>@inf_ann_64]
 inferred pure: [b=inf_b_66; inf_ann_64=@M; inf_ann_68=@M]


Entail (4) : Valid. 

 <1>emp&b!=null & a=inf_a_84 & inf_m_88=m & inf_ann_87<:@I & inf_ann_83<:@I & b=inf_b_85&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_88>@inf_ann_87; 
                 y::node<inf_a_84,inf_b_85>@inf_ann_83]
 inferred pure: [b=inf_b_85; inf_ann_83<:@I; inf_ann_87<:@I]


Entail (5) : Valid. 

 <1>emp&b!=null & a=inf_a_103 & inf_m_107=m & inf_ann_106=@M & inf_ann_102=@M & b=inf_b_104&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_107>@inf_ann_106; 
                 y::node<inf_a_103,inf_b_104>@inf_ann_102]
 inferred pure: [b=inf_b_104; inf_ann_102=@M; inf_ann_106=@M]


!!! dumping for sleek_dump(fail)
Entail (6) : Fail.


Entail (7) : Valid. 

 <1>(exists flted_7_169,q_185,flted_7_183: q_185::ll<flted_7_183>@M&flted_7_169=flted_7_183+1 & n=flted_7_169+1 & n=2&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=2; n!=0; n!=1]


!!! dumping for sleek_dump(fail)
Entail (8) : Fail.


Entail (9) : Valid. 

 <1>emp&n=m+1&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (10) : Valid. 

 <1>emp&n=m+1&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=0]

Stop Omega... 168 invocations 
SAT Count   : 172
SAT % Hit   : 68.6%
IMPLY Count : 151
IMPLY % Hit : 71.52%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.243511,458)
Total verification time: 0.18 second(s)
	Time spent in main process: 0.13 second(s)
	Time spent in child processes: 0.05 second(s)

