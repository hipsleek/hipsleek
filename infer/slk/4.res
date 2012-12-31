Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (2) : Valid. 

 <1>EXISTS(flted_7_51: b::ll<flted_7_51>@M[Orig]&flted_7_51+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (3) : Valid. 

 <1>emp&b!=null & a=inf_a_67 & m=inf_m_71 & inf_ann_70<=0 & inf_ann_66<=0 & b=inf_b_68&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_71>@inf_ann_70[Orig][LHSCase]; 
                y::node<inf_a_67,inf_b_68>@inf_ann_66[Orig]]
 inferred pure: [b=inf_b_68; inf_ann_66<=0; inf_ann_70<=0]


Entail (4) : Valid. 

 <1>emp&b!=null & a=inf_a_89 & m=inf_m_93 & inf_ann_92<=1 & inf_ann_88<=1 & b=inf_b_90&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_93>@inf_ann_92[Orig][LHSCase]; 
                y::node<inf_a_89,inf_b_90>@inf_ann_88[Orig]]
 inferred pure: [b=inf_b_90; inf_ann_88<=1; inf_ann_92<=1]


Entail (5) : Valid. 

 <1>emp&b!=null & a=inf_a_111 & m=inf_m_115 & inf_ann_114<=0 & inf_ann_110<=0 & b=inf_b_112&{FLOW,(19,20)=__norm}[]
 inferred heap: [b::ll<inf_m_115>@inf_ann_114[Orig][LHSCase]; 
                y::node<inf_a_111,inf_b_112>@inf_ann_110[Orig]]
 inferred pure: [b=inf_b_112; inf_ann_110<=0; inf_ann_114<=0]


Entail (6) : Fail.(may) cause: true |-  y!=null. LOCS:[0] (may-bug)


Entail (7) : Valid. 

 <1>EXISTS(flted_7_166,q_182,flted_7_180: q_182::ll<flted_7_180>@M[Orig]&flted_7_180+1=flted_7_166 & flted_7_166+1=n & n=2&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=2; n!=0; n!=1]


Entail (8) : Fail.(may) cause:OrR[15.1 q_218=null & q=q_218 |-  q!=null (must-bug).,valid]


Entail (9) : Valid. 

 <1>emp&m+1=n&{FLOW,(19,20)=__norm}[]
 inferred pure: [x!=null]


Entail (10) : Valid. 

 <1>emp&m+1=n&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=0]

Stop Omega... 147 invocations 
