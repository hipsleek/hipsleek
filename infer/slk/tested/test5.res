Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (2) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=0]


!!! dumping for sleek_dump(fail)
Entail (3) : Fail.


Entail (4) : Valid. 

 <1>emp&Anon_18=1 & Anon_17=inf_Anon_117 & Anon_19=inf_Anon_121 & inf_ann_120=@M & inf_ann_116=@M & inf_flted_29_122=null & b=inf_b_118&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_Anon_121,inf_flted_29_122>@inf_ann_120; 
                 x::node<inf_Anon_117,inf_b_118>@inf_ann_116]
 inferred pure: [b=inf_b_118; inf_flted_29_122=null; inf_ann_116=@M; 
                 inf_ann_120=@M]


!!! dumping for sleek_dump(fail)
Entail (5) : Fail.

Stop Omega... 126 invocations 
SAT Count   : 92
SAT % Hit   : 35.86%
IMPLY Count : 72
IMPLY % Hit : 63.88%
Time(cache overhead) : 0.02 (seconds)

!!! log(small):(0.202655,225)
Total verification time: 0.16 second(s)
	Time spent in main process: 0.11 second(s)
	Time spent in child processes: 0.05 second(s)

