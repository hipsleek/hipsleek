Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&q=null & inf_n_28=n & inf_ann_27=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [q::ll<inf_n_28>@inf_ann_27]
 inferred pure: [inf_ann_27=@M]


Entail (2) : Valid. 

 <1>emp&q=null & n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]


Entail (3) : Valid. 

 <1>emp&q!=null & inf_n_41=n & inf_ann_40=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [q::ll<inf_n_41>@inf_ann_40]
 inferred pure: [inf_ann_40=@M]


!!! dumping for sleek_dump(fail)
Entail (4) : Fail.


Entail (5) : Valid. 

 <1>emp&n=0 & inf_ann_59=@M & inf_n_60<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [q::ll<inf_n_60>@inf_ann_59]
 inferred pure: [inf_n_60<=0; inf_ann_59=@M]


!!! dumping for sleek_dump(fail)
Entail (6) : Fail.


Entail (7) : Valid. 

 <1>emp&n=0 & inf_ann_84=@M & inf_n_85=n&{FLOW,(19,20)=__norm}[]
 inferred heap: [q::ll<inf_n_85>@inf_ann_84]
 inferred pure: [inf_n_85=n; inf_ann_84=@M]


Entail (8) : Valid. 

 <1>emp&n=0 & inf_ann_98=@M & inf_n_99=n&{FLOW,(19,20)=__norm}[]
 inferred heap: [q::ll<inf_n_99>@inf_ann_98]
 inferred pure: [inf_n_99=n; inf_ann_98=@M]


!!! dumping for sleek_dump(fail)
Entail (9) : Fail.

Stop Omega... 130 invocations 
SAT Count   : 100
SAT % Hit   : 59.%
IMPLY Count : 82
IMPLY % Hit : 56.09%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.089532,271)
Total verification time: 0.13 second(s)
	Time spent in main process: 0.09 second(s)
	Time spent in child processes: 0.04 second(s)

