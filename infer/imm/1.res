Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>x::node<p,q>@M[Orig]&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (2): Valid. 

<1>x::node<p,q>@M[Orig]&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (3): Valid. 

<1>x::node<p,q>@L[Orig]&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (4): Valid. 

<1>true&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (5): Valid. 

<1>true&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (6): Valid. 

<1>x::node<p,q>@M[Orig]&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (7): Valid. 

<1>true&a=p & b=q&{FLOW,(17,18)=__norm}

Entail  (8): Valid. 

<1>EXISTS(flted_7_97: b::ll<flted_7_97>@M[Orig]&flted_7_97+1=n&{FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (9): Valid. 

<1>EXISTS(flted_7_116: b::ll<flted_7_116>@I[Orig]&flted_7_116+1=n&{FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (10): Valid. 

<1>EXISTS(flted_7_135: b::ll<flted_7_135>@I[Orig]&flted_7_135+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (11): Valid. 

<1>EXISTS(flted_7_154: b::ll<flted_7_154>@M[Orig]&flted_7_154+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (12): Valid. 

<1>EXISTS(flted_7_174: x::node<a,b>@M[Orig] * b::ll<flted_7_174>@M[Orig]&flted_7_174+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (13): Valid. 

<1>EXISTS(flted_7_197,flted_7_216: x::node<a,b>@L[Orig] * b::node<Anon_12,Anon_13>@L[Orig] * Anon_13::ll<flted_7_216>@L[Orig]&flted_7_216+1=flted_7_197 & flted_7_197+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; n!=1]

Entail  (14): Fail.(may) cause:lor[911 : mismatched annotation,valid]


Entail  (15): Valid. 

<1>EXISTS(flted_7_280,flted_7_299: x::node<a,b>@L[Orig] * b::node<Anon_16,Anon_17>@L[Orig] * Anon_17::ll<flted_7_299>@L[Orig]&flted_7_299+1=flted_7_280 & flted_7_280+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (16): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(flted_7_323,q_343,flted_7_341: Hole[326] * q_343::ll<flted_7_341>@L[Orig]&flted_7_341+1=flted_7_323 & flted_7_323+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (17): Valid. 

<1>EXISTS(flted_7_364,flted_7_383: x::node<a,b>@L[Orig] * b::node<Anon_20,Anon_21>@L[Orig] * Anon_21::ll<flted_7_383>@L[Orig]&flted_7_383+1=flted_7_364 & flted_7_364+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (18): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(q_408,flted_7_406: q_408::ll<flted_7_406>@L[Orig]&flted_7_406+1=n & 1<n&{FLOW,(17,18)=__norm})

Stop Omega... 48 invocations 
