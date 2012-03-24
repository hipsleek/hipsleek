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

<1>EXISTS(flted_9_95: b::ll<flted_9_95>@M[Orig]&flted_9_95+1=n&{FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (9): Valid. 

<1>EXISTS(flted_9_114: b::ll<flted_9_114>@I[Orig]&flted_9_114+1=n&{FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (10): Valid. 

<1>EXISTS(flted_9_133: b::ll<flted_9_133>@I[Orig]&flted_9_133+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (11): Valid. 

<1>EXISTS(flted_9_152: b::ll<flted_9_152>@M[Orig]&flted_9_152+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (12): Valid. 

<1>EXISTS(flted_9_172: x::node<a,b>@M[Orig] * b::ll<flted_9_172>@M[Orig]&flted_9_172+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (13): Valid. 

<1>EXISTS(flted_9_195,flted_9_214: x::node<a,b>@L[Orig] * b::node<Anon_12,Anon_13>@L[Orig] * Anon_13::ll<flted_9_214>@L[Orig]&flted_9_214+1=flted_9_195 & flted_9_195+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0; n!=1]

Entail  (14): Fail.(may) cause:lor[911 : mismatched annotation,valid]


Entail  (15): Valid. 

<1>EXISTS(flted_9_278,flted_9_297: x::node<a,b>@L[Orig] * b::node<Anon_16,Anon_17>@L[Orig] * Anon_17::ll<flted_9_297>@L[Orig]&flted_9_297+1=flted_9_278 & flted_9_278+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (16): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(flted_9_321,q_341,flted_9_339: Hole[324] * q_341::ll<flted_9_339>@L[Orig]&flted_9_339+1=flted_9_321 & flted_9_321+1=n & 1<n&{FLOW,(17,18)=__norm})

Entail  (17): Fail.(must) cause:911 : mismatched annotation

<1>EXISTS(q_363,flted_9_361: q_363::ll<flted_9_361>@L[Orig]&flted_9_361+1=n & 1<n&{FLOW,(17,18)=__norm})

Stop Omega... 45 invocations 
