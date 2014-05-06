Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&q_41=null & n=0+1 & inf_m_51=m & inf_ann_50=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::ll<inf_m_51>@inf_ann_50]
 inferred pure: [inf_ann_50=@M]


Entail (2) : Valid. 

 <1>(exists flted_22_68: z::node<flted_22_68>@M&q_70=null & flted_22_68=null & n=0+1 & inf_m_80=m & inf_ann_79=@M&{FLOW,(19,20)=__norm})[]
 inferred heap: [y::ll<inf_m_80>@inf_ann_79]
 inferred pure: [inf_ann_79=@M]


Entail (3) : Valid. 

 <1>emp&a=y & inf_ann_90=@M & inf_flted_25_91=null&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::lseg<inf_flted_25_91>@inf_ann_90]
 inferred pure: [inf_flted_25_91=null; inf_ann_90=@M]


Entail (4) : Valid. 

 <1>emp&a=y & inf_n_103=n & inf_ann_102=@M&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::ll<inf_n_103>@inf_ann_102]
 inferred pure: [inf_ann_102=@M]


Entail (5) : Valid. 

 <1>emp&q_117=z & inf_ann_122=@M & inf_p_123=null & inf_p_123!=x & inf_ann_136=@M & z=null & ((y=null | (inf_flted_31_137=null & y!=null)))&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::lseg<inf_flted_31_137>@inf_ann_136; 
                 z::lseg<inf_p_123>@inf_ann_122]
 inferred pure: [(y=null | (inf_flted_31_137=null & y!=null)); z=null; 
                 inf_ann_136=@M; inf_p_123=null; inf_ann_122=@M]

Stop Omega... 211 invocations 
SAT Count   : 133
SAT % Hit   : 39.84%
IMPLY Count : 137
IMPLY % Hit : 55.47%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.268876,399)
Total verification time: 0.22 second(s)
	Time spent in main process: 0.13 second(s)
	Time spent in child processes: 0.09 second(s)

