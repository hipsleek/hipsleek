Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&a=inf_a_30 & b=inf_b_31 & inf_ann_29=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_a_30,inf_b_31>@inf_ann_29]
 inferred pure: [inf_ann_29=@M]


Entail (2) : Valid. 

 <1>emp&inf_n_36=n & inf_ann_35=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::ll<inf_n_36>@inf_ann_35]
 inferred pure: [inf_ann_35=@M]


Entail (3) : Valid. 

 <1>emp&a=inf_a_44 & b=inf_b_45 & c=inf_c_47 & d=inf_d_48 & inf_ann_46=@M & inf_ann_43=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_b_45::node<inf_c_47,inf_d_48>@inf_ann_46; 
                 y::node<inf_a_44,inf_b_45>@inf_ann_43]
 inferred pure: [inf_ann_43=@M; inf_ann_46=@M]


Entail (4) : Valid. 

 <1>emp&a=inf_a_55 & b=inf_b_56 & inf_m_58=m & inf_ann_57=@M & inf_ann_54=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_b_56::ll<inf_m_58>@inf_ann_57; 
                 y::node<inf_a_55,inf_b_56>@inf_ann_54]
 inferred pure: [inf_ann_54=@M; inf_ann_57=@M]


Entail (5) : Valid. 

 <1>emp&x=y & inf_n_65=n & inf_ann_64=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [x::ll<inf_n_65>@inf_ann_64]
 inferred pure: [inf_ann_64=@M]


Entail (6) : Valid. 

 <1>emp&n=0 & x=y & inf_ann_75=@M & inf_n_76<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [x::ll<inf_n_76>@inf_ann_75]
 inferred pure: [inf_n_76<=0; inf_ann_75=@M]


Entail (7) : Valid. 

 <1>emp&x=y & inf_n_86=n & inf_ann_85=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [x::ll<inf_n_86>@inf_ann_85]
 inferred pure: [inf_ann_85=@M]


Entail (8) : Valid. 

 <1>emp&a=ia & b=ib&{FLOW,(19,20)=__norm}[]


Entail (9) : Valid. 

 <1>emp&inf_ann_104=@M & inf_flted_43_106=null & 1<=inf_a_105&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_a_105,inf_flted_43_106>@inf_ann_104]
 inferred pure: [1<=inf_a_105; inf_flted_43_106=null; inf_ann_104=@M]


Entail (10) : Valid. 

 <1>(exists flted_47_132: emp&flted_47_132=null & 1<=aa&{FLOW,(19,20)=__norm})[]
 inferred pure: [1<=aa]


Entail (11) : Valid. 

 <1>emp&m=n&{FLOW,(19,20)=__norm}[]


Entail (12) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (13) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [y!=null]

Stop Omega... 183 invocations 
SAT Count   : 117
SAT % Hit   : 52.13%
IMPLY Count : 122
IMPLY % Hit : 59.01%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.133299,374)
Total verification time: 0.14 second(s)
	Time spent in main process: 0.1 second(s)
	Time spent in child processes: 0.04 second(s)

