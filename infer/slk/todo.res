Starting Omega...oc

!!! dumping for sleek_dump(fail)
Entail (1) : Fail.


!!! dumping for sleek_dump(fail)
Entail (2) : Fail.


Entail (3) : Valid. 

 <1>emp&b!=null & a=inf_a_72 & inf_m_76=m & inf_ann_75=@M & inf_ann_71=@M & b=inf_b_73&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_76>@inf_ann_75; 
                 y::node<inf_a_72,inf_b_73>@inf_ann_71]
 inferred pure: [b=inf_b_73; inf_ann_71=@M; inf_ann_75=@M]


!!! dumping for sleek_dump(fail)
Entail (4) : Fail.


Entail (5) : Valid. 

 <1>emp&c=i & 1<=i&{FLOW,(19,20)=__norm}[]
 inferred pure: [1<=i]


Entail (6) : Valid. 

 <1>(exists flted_7_133: b::ll<flted_7_133>@M&n=flted_7_133+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [(n!=0 | x!=null)]

Stop Omega... 101 invocations 
SAT Count   : 86
SAT % Hit   : 53.48%
IMPLY Count : 82
IMPLY % Hit : 60.97%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.091425,227)
Total verification time: 0.12 second(s)
	Time spent in main process: 0.08 second(s)
	Time spent in child processes: 0.04 second(s)

