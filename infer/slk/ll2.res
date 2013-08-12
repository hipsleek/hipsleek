Starting Omega...oc

Entail (1) : Valid. 

 <1>
    emp&Anon_53=1 & p=q_54 & inf_ann_59=@M & m=inf_flted_7_60+1&
    {FLOW,(19,20)=__norm}[]
    or emp&Anon_70=1 & Anon_76=2 & q=q_71 & p=q_77 & inf_ann_82=@M & 
       m=inf_flted_7_83+1+1&{FLOW,(19,20)=__norm}[]
    
 inferred heap: [p::ll<inf_flted_7_60>@inf_ann_59; 
                 p::ll<inf_flted_7_83>@inf_ann_82]
 inferred pure: [inf_ann_59=@M; inf_ann_82=@M]


Entail (2) : Valid. 

 <1>
    (exists flted_7_120,q_136,flted_7_134: q_136::ll<flted_7_134>@M&
    flted_7_120=flted_7_134+1 & m=flted_7_120+1 & m=2&
    {FLOW,(19,20)=__norm})[]
    or (exists q_160,flted_7_158: q_160::ll<flted_7_158>@M&m=flted_7_158+1 & 
       Anon_14=1 & q=r & m=1&{FLOW,(19,20)=__norm})[]
    or p::ll<m>@M&Anon_12=Anon_14 & r=t & Anon_13=Anon_15 & m=0&
       {FLOW,(19,20)=__norm}[]
    
 inferred pure: [m=2; m!=0; m!=1; m=1; m!=0; m=0]


Entail (3) : Valid. 

 <1>(exists q_194,flted_7_192: q_194::ll<flted_7_192>@M&n=flted_7_192+1 & x!=null & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [0>n; n=1]


Entail (4) : Valid. 

 <1>x::ll<n>@M&n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]
<2>(exists q_223,flted_7_221: q_223::ll<flted_7_221>@M&n=flted_7_221+1 & n=1&{FLOW,(19,20)=__norm})[]
inferred pure: [n=1; n!=0]


Entail (5) : Valid. 

 <1>x::ll<n>@M&n=0&{FLOW,(19,20)=__norm}[]


Entail (6) : Valid. 

 <1>x::ll<n>@M&n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]
<2>(exists q_262,flted_7_260: q_262::ll<flted_7_260>@M&n=flted_7_260+1 & n=1&{FLOW,(19,20)=__norm})[]
inferred pure: [n=1; n!=0]


Entail (7) : Valid. 

 <1>
    (exists flted_7_292,q_308,flted_7_306: q_308::ll<flted_7_306>@M&
    flted_7_292=flted_7_306+1 & n=flted_7_292+1 & x!=null & n=2&
    {FLOW,(19,20)=__norm})[]
    or x::ll<n>@M&x=null&{FLOW,(19,20)=__norm}[]
    
 inferred pure: [n=2; n!=1]

Stop Omega... 191 invocations 
SAT Count   : 166
SAT % Hit   : 63.85%
IMPLY Count : 137
IMPLY % Hit : 70.07%
Time(cache overhead) : 0.03 (seconds)

!!! log(small):(0.190611,464)
Total verification time: 0.2 second(s)
	Time spent in main process: 0.15 second(s)
	Time spent in child processes: 0.05 second(s)

