Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&a=p & b=q & v<=1&{FLOW,(17,18)=__norm}
inferred pure: [v<=1]

Entail  (2): Valid. 

<1>true&a=p & b=q & v<=0&{FLOW,(17,18)=__norm}
inferred pure: [v<=0]

Entail  (3): Valid. 

<1>EXISTS(flted_7_60: b::ll<flted_7_60>@v[Orig]&flted_7_60+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=0]

Entail  (4): Valid. 

<1>EXISTS(flted_7_80: b::ll<flted_7_80>@v[Orig]&flted_7_80+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=1]

Entail  (5): Valid. 

<1>EXISTS(flted_7_100: b::ll<flted_7_100>@v[Orig]&flted_7_100+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=1]

Entail  (6): Valid. 

<1>EXISTS(flted_7_120: b::ll<flted_7_120>@v[Orig]&flted_7_120+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=0]

Entail  (7): Valid. 

<1>EXISTS(flted_7_141: x::node<a,b>@v[Orig] * b::ll<flted_7_141>@v[Orig]&flted_7_141+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (8): Valid. 

<1>EXISTS(flted_7_161: b::ll<flted_7_161>@M[Orig]&flted_7_161+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (9): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(flted_7_184,q_204,flted_7_202: Hole[187] * q_204::ll<flted_7_202>@L[Orig]&flted_7_202+1=flted_7_184 & flted_7_184+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (10): Valid. 

<1>EXISTS(flted_7_226,flted_7_240: Anon_15::ll<flted_7_240>@v1[Orig]&flted_7_240+1=flted_7_226 & flted_7_226+1=n & 1<n & v1<:v2 & v2<=1&{FLOW,(17,18)=__norm})
inferred pure: [v2<=1]

Entail  (11): Valid. 

<1>EXISTS(flted_7_263,flted_7_277: Anon_17::ll<flted_7_277>@I[Orig]&flted_7_277+1=flted_7_263 & flted_7_263+1=n & 1<n & @I<:v2&{FLOW,(17,18)=__norm})

Entail  (12): Valid. 

<1>true&v1<:v2 & c=a & d=b&{FLOW,(17,18)=__norm}

Entail  (13): Valid. 

<1>true&v1<:v2&{FLOW,(17,18)=__norm}

Entail  (14): Valid. 

<1>true&@I<:v2&{FLOW,(17,18)=__norm}

Entail  (15): Valid. 

<1>true&v2<=1&{FLOW,(17,18)=__norm}
inferred pure: [v2<=1]

Entail  (16): Valid. 

<1>true&v2<=0&{FLOW,(17,18)=__norm}
inferred pure: [v2<=0]

Entail  (17): Valid. 

<1>true&@L<:v2&{FLOW,(17,18)=__norm}

Stop Omega... 139 invocations 
