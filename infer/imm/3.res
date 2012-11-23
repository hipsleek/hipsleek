Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&a=p & b=q & v<=1&{FLOW,(17,18)=__norm}
inferred pure: [v<=1]

Entail  (2): Valid. 

<1>true&a=p & b=q & v<=0&{FLOW,(17,18)=__norm}
inferred pure: [v<=0]

Entail  (3): Valid. 

<1>EXISTS(flted_7_70: b::ll<flted_7_70>@v[Orig]&flted_7_70+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=0]

Entail  (4): Valid. 

<1>EXISTS(flted_7_90: b::ll<flted_7_90>@v[Orig]&flted_7_90+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=1]

Entail  (5): Valid. 

<1>EXISTS(flted_7_110: b::ll<flted_7_110>@v[Orig]&flted_7_110+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=1]

Entail  (6): Valid. 

<1>EXISTS(flted_7_130: b::ll<flted_7_130>@v[Orig]&flted_7_130+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=0]

Entail  (7): Valid. 

<1>EXISTS(flted_7_151: x::node<a,b>@v[Orig] * b::ll<flted_7_151>@v[Orig]&flted_7_151+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (8): Valid. 

<1>EXISTS(flted_7_171: b::ll<flted_7_171>@M[Orig]&flted_7_171+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (9): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(flted_7_194,q_214,flted_7_212: Hole[197] * q_214::ll<flted_7_212>@L[Orig]&flted_7_212+1=flted_7_194 & flted_7_194+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (10): Valid. 

<1>EXISTS(flted_7_236,flted_7_250: Anon_15::ll<flted_7_250>@v1[Orig]&flted_7_250+1=flted_7_236 & flted_7_236+1=n & 1<n & v1<=v2 & v1<=1&{FLOW,(17,18)=__norm})
inferred pure: [v1<=1; v1<=v2]

Entail  (11): Valid. 

<1>EXISTS(flted_7_273,flted_7_287: Anon_17::ll<flted_7_287>@I[Orig]&flted_7_287+1=flted_7_273 & flted_7_273+1=n & 1<n & 1<=v2&{FLOW,(17,18)=__norm})
inferred pure: [1<=v2]

Entail  (12): Valid. 

<1>true&c=a & d=b & v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2]

Entail  (13): Valid. 

<1>true&v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2]

Entail  (14): Valid. 

<1>true&1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [1<=v2]

Entail  (15): Valid. 

<1>true&v2<=1&{FLOW,(17,18)=__norm}
inferred pure: [v2<=1]

Entail  (16): Valid. 

<1>true&v2<=0&{FLOW,(17,18)=__norm}
inferred pure: [v2<=0]

Entail  (17): Valid. 

<1>true&2<=v2&{FLOW,(17,18)=__norm}
inferred pure: [2<=v2]

Entail  (18): Valid. 

<1>true&a=Anon_18 & b=q & v1<:v2 & Anon_20=Anon_19 & Anon_21=r & v1<=1&{FLOW,(17,18)=__norm}
inferred pure: [v1<=1]

Entail  (19): Valid. 

<1>true&a=Anon_22 & b=q & Anon_24=Anon_23 & Anon_25=r & v1<=1 & v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2; v1<=1]

Entail  (20): Valid. 

<1>true&v1<:I & v1<:v2 & a=Anon_26 & b=q&{FLOW,(17,18)=__norm}

Entail  (21): Valid. 

<1>true&a=Anon_27 & b=q & v1<=1&{FLOW,(17,18)=__norm}
inferred pure: [v1<=1]

Stop Omega... 253 invocations 
