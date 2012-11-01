Starting Omega...oc

Entail (1) : Valid. 

 <1>
    emp&Anon_52=1 & q_53=p & inf_ann_58<=0 & inf_flted_7_59+1=m&
    {FLOW,(19,20)=__norm}[]
    or emp&Anon_69=1 & Anon_75=2 & q_70=q & q_76=p & inf_ann_81<=0 & 
       inf_flted_7_82+1+1=m&{FLOW,(19,20)=__norm}[]
    
 inferred heap: [p::ll<inf_flted_7_59>@inf_ann_58[Orig]; 
                p::ll<inf_flted_7_82>@inf_ann_81[Orig]]
 inferred pure: [inf_ann_58<=0; inf_ann_81<=0]


Entail (2) : Valid. 

 <1>
    EXISTS(flted_7_123,q_139,flted_7_137: q_139::ll<flted_7_137>@M[Orig]&
    flted_7_137+1=flted_7_123 & flted_7_123+1=m & m=2&
    {FLOW,(19,20)=__norm})[]
    or EXISTS(q_163,flted_7_161: q_163::ll<flted_7_161>@M[Orig]&flted_7_161+
       1=m & Anon_14=1 & r=q & m=1&{FLOW,(19,20)=__norm})[]
    or p::ll<m>@M[Orig][LHSCase]&Anon_14=Anon_12 & r=t & Anon_15=Anon_13 & 
       m=0&{FLOW,(19,20)=__norm}[]
    
 inferred pure: [m=2; m!=0; m!=1; m=1; m!=0; m=0]


Entail (3) : Valid. 

 <1>EXISTS(q_210,flted_7_208: q_210::ll<flted_7_208>@M[Orig]&flted_7_208+1=n & x!=null & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0; n=1]


Entail (4) : Valid. 

 <1>x::ll<n>@M[Orig][LHSCase]&n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]
<2>EXISTS(q_244,flted_7_242: q_244::ll<flted_7_242>@M[Orig]&flted_7_242+1=n & n=1&{FLOW,(19,20)=__norm})[]
inferred pure: [n=1; n!=0]


Entail (5) : Valid. 

 <1>x::ll<n>@M[Orig][LHSCase]&n=0&{FLOW,(19,20)=__norm}[]


Entail (6) : Valid. 

 <1>x::ll<n>@M[Orig][LHSCase]&n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]
<2>EXISTS(q_302,flted_7_300: q_302::ll<flted_7_300>@M[Orig]&flted_7_300+1=n & n=1&{FLOW,(19,20)=__norm})[]
inferred pure: [n=1; n!=0]


Entail (7) : Valid. 

 <1>
    EXISTS(flted_7_338,q_354,flted_7_352: q_354::ll<flted_7_352>@M[Orig]&
    flted_7_352+1=flted_7_338 & flted_7_338+1=n & x!=null & n=2&
    {FLOW,(19,20)=__norm})[]
    or x::ll<n>@M[Orig][LHSCase]&x=null&{FLOW,(19,20)=__norm}[]
    
 inferred pure: [n=2; n!=1]

Stop Omega... 144 invocations 
