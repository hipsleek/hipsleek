Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&a=inf_a_29 & b=inf_b_30 & inf_ann_28<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_a_29,inf_b_30>@inf_ann_28[Orig]]
 inferred pure: [inf_ann_28<=0]


Entail (2) : Valid. 

 <1>emp&n=inf_n_35 & inf_ann_34<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::ll<inf_n_35>@inf_ann_34[Orig][LHSCase]]
 inferred pure: [inf_ann_34<=0]


Entail (3) : Valid. 

 <1>emp&a=inf_a_43 & b=inf_b_44 & c=inf_c_46 & d=inf_d_47 & inf_ann_45<=0 & inf_ann_42<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_b_44::node<inf_c_46,inf_d_47>@inf_ann_45[Orig]; 
                y::node<inf_a_43,inf_b_44>@inf_ann_42[Orig]]
 inferred pure: [inf_ann_42<=0; inf_ann_45<=0]


Entail (4) : Valid. 

 <1>emp&a=inf_a_54 & b=inf_b_55 & m=inf_m_57 & inf_ann_56<=0 & inf_ann_53<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [inf_b_55::ll<inf_m_57>@inf_ann_56[Orig][LHSCase]; 
                y::node<inf_a_54,inf_b_55>@inf_ann_53[Orig]]
 inferred pure: [inf_ann_53<=0; inf_ann_56<=0]


Entail (5) : Valid. 

 <1>emp&x=y & n=inf_n_62 & inf_ann_61<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [x::ll<inf_n_62>@inf_ann_61[Orig][LHSCase]]
 inferred pure: [inf_ann_61<=0]


Entail (6) : Valid. 

 <1>emp&n=0 & x=y & inf_ann_73<=0 & inf_n_74<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [x::ll<inf_n_74>@inf_ann_73[Orig][LHSCase]]
 inferred pure: [inf_n_74<=0; inf_ann_73<=0]


Entail (7) : Valid. 

 <1>emp&x=y & n=inf_n_84 & inf_ann_83<=0&{FLOW,(19,20)=__norm}[]
 inferred heap: [x::ll<inf_n_84>@inf_ann_83[Orig][LHSCase]]
 inferred pure: [inf_ann_83<=0]


Entail (8) : Valid. 

 <1>emp&a=ia & b=ib&{FLOW,(19,20)=__norm}[]


Entail (9) : Valid. 

 <1>emp&inf_ann_109<=0 & inf_flted_43_111=null & 1<=inf_a_110&{FLOW,(19,20)=__norm}[]
 inferred heap: [y::node<inf_a_110,inf_flted_43_111>@inf_ann_109[Orig]]
 inferred pure: [1<=inf_a_110; inf_flted_43_111=null; inf_ann_109<=0]


Entail (10) : Valid. 

 <1>EXISTS(flted_47_144: emp&flted_47_144=null & 1<=aa&{FLOW,(19,20)=__norm})[]
 inferred pure: [1<=aa]


Entail (11) : Valid. 

 <1>emp&n=m&{FLOW,(19,20)=__norm}[]


Entail (12) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (13) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [y!=null]

Stop Omega... 170 invocations 
