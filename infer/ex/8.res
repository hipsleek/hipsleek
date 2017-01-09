Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true & q_39=null & 0+1=n & m=inf_m_49 & inf_ann_48<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_m_49>@inf_ann_48[Orig][LHSCase]]
inferred pure: [inf_ann_48<=0]

Entail  (2): Valid. 

<1>EXISTS(flted_22_66: z::node<flted_22_66>@M[Orig] & q_68=null & flted_22_66=null & 0+1=n & m=inf_m_78 & inf_ann_77<=0 & {FLOW,(17,18)=__norm})
inferred heap: [y::ll<inf_m_78>@inf_ann_77[Orig][LHSCase]]
inferred pure: [inf_ann_77<=0]

Entail  (3): Valid. 

<1>true & a=y & inf_ann_88<=0 & inf_flted_25_89=null & {FLOW,(17,18)=__norm}
inferred heap: [y::lseg<inf_flted_25_89>@inf_ann_88[Orig][LHSCase]]
inferred pure: [inf_flted_25_89=null; inf_ann_88<=0]

Entail  (4): Valid. 

<1>true & a=y & n=inf_n_101 & inf_ann_100<=0 & {FLOW,(17,18)=__norm}
inferred heap: [y::ll<inf_n_101>@inf_ann_100[Orig][LHSCase]]
inferred pure: [inf_ann_100<=0]

Entail  (5): Valid. 

<1>true & q_115=z & inf_ann_120<=0 & inf_p_121=null & x!=inf_p_121 & inf_ann_127<=0 & (inf_flted_31_128=null & y!=null | y=null) & z=null & {FLOW,(17,18)=__norm}
inferred heap: [y::lseg<inf_flted_31_128>@inf_ann_127[Orig][LHSCase]; 
               z::lseg<inf_p_121>@inf_ann_120[Orig]]
inferred pure: [z=null; inf_flted_31_128=null & y!=null | y=null; 
               inf_ann_127<=0; inf_p_121=null; inf_ann_120<=0]

Stop Omega... 236 invocations 
