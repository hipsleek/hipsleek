Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&a=p & b=q & v<=1&{FLOW,(17,18)=__norm}
inferred pure: [v<=1]

Entail  (2): Valid. 

<1>true&a=p & b=q & v<=0&{FLOW,(17,18)=__norm}
inferred pure: [v<=0]

Entail  (3): Valid. 

<1>EXISTS(flted_7_56: b::ll<flted_7_56>@v[Orig]&flted_7_56+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=0]

Entail  (4): Valid. 

<1>EXISTS(flted_7_76: b::ll<flted_7_76>@v[Orig]&flted_7_76+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [x!=null; v<=1]

Entail  (5): Valid. 

<1>EXISTS(flted_7_96: b::ll<flted_7_96>@v[Orig]&flted_7_96+1=n & v<=1&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=1]

Entail  (6): Valid. 

<1>EXISTS(flted_7_116: b::ll<flted_7_116>@v[Orig]&flted_7_116+1=n & v<=0&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; v<=0]

Entail  (7): Valid. 

<1>EXISTS(flted_7_137: x::node<a,b>@v[Orig] * b::ll<flted_7_137>@v[Orig]&flted_7_137+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (8): Valid. 

<1>EXISTS(flted_7_157: b::ll<flted_7_157>@M[Orig]&flted_7_157+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (9): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(flted_7_180,q_200,flted_7_198: Hole[183] * q_200::ll<flted_7_198>@L[Orig]&flted_7_198+1=flted_7_180 & flted_7_180+1=n & 1<n&{FLOW,(17,18)=__norm})

Stop Omega... 86 invocations 
