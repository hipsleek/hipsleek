Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & v=inf_43 & q=inf_44 & {FLOW,(17,18)=__norm}
inferred heap: [x::node<inf_43,inf_44>@M[Orig]]

Entail  (2): Valid. 
<1>true & n=inf_48 & {FLOW,(17,18)=__norm}
inferred heap: [x::ll<inf_48>@M[Orig][LHSCase]]

Entail  (3): Valid. 
<1>true & Anon_59=1 & q_60=p & inf_flted_7_65+1=n & {FLOW,(17,18)=__norm}
inferred heap: [q_60::ll<inf_flted_7_65>@M[Orig]]
inferred pure: [q_60=p]

Entail  (4): Valid. 
<1>EXISTS(flted_7_87: p::ll<flted_7_87>@M[Orig] & flted_7_87+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (5): Valid. 
<1>EXISTS(q_112,flted_7_110: q_112::ll<flted_7_110>@M[Orig] & flted_7_110+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (6): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (7): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (8): Valid. 
<1>EXISTS(q_177,flted_7_175: q_177::ll<flted_7_175>@M[Orig] & flted_7_175+1=n & 0<n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n=1]

Entail  (9): Valid. 
<1>EXISTS(q_206,flted_7_204: q_206::ll<flted_7_204>@M[Orig] & flted_7_204+1=n & n<=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (10): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [n!=0]

Entail  (11): Valid. 
<1>true & Anon_247=1 & Anon_253=3 & q_248=x2 & q_254=p & inf_flted_7_259+1+1=n & {FLOW,(17,18)=__norm}
inferred heap: [q_254::ll<inf_flted_7_259>@M[Orig]]
inferred pure: [q_254=p]

Entail  (12): Valid. 
<1>EXISTS(flted_7_283,flted_7_297: p::ll<flted_7_297>@M[Orig] & flted_7_297+1=flted_7_283 & flted_7_283+1=n & {FLOW,(17,18)=__norm})
inferred pure: [n!=1; n!=0]

Entail  (13): Valid. 
<1>true & Anon_318=1 & Anon_324=3 & q_319=x2 & q_325=p & inf_flted_7_330+1+1=n & inf_flted_7_330=2 & {FLOW,(17,18)=__norm}
inferred heap: [q_325::ll<inf_flted_7_330>@M[Orig]]
inferred pure: [q_325=p; inf_flted_7_330=2]

Entail  (14): Valid. 
<1>true & a=1 & x2=p & b=inf_350 & q=inf_351 & inf_351=null & {FLOW,(17,18)=__norm}
inferred heap: [x2::node<inf_350,inf_351>@M[Orig]]
inferred pure: [x2=p; inf_351=null]

Entail  (15): Fail.(must) cause:(failure_code=213)  flted_53_368=1 |-  flted_53_368=2 (must-bug).
<1>EXISTS(flted_53_368: true & flted_53_368=1 & x2=p & b=inf_371 & q=inf_372 & {FLOW,(1,2)=__Error})
inferred heap: [x2::node<inf_371,inf_372>@M[Orig]]
inferred pure: [x2=p]

Entail  (16): Valid. 
<1>EXISTS(flted_56_394: true & flted_56_394=1 & x2=p & q=inf_399 & inf_flted_56_398=3 & inf_399=null & {FLOW,(17,18)=__norm})
inferred heap: [x2::node<inf_flted_56_398,inf_399>@M[Orig]]
inferred pure: [x2=p; inf_flted_56_398=3 & inf_399=null]

Entail  (17): Valid. 
<1>EXISTS(flted_59_422: true & flted_59_422=1 & x2=p & m=inf_425 & 4<=inf_425 & {FLOW,(17,18)=__norm})
inferred heap: [x2::ll<inf_425>@M[Orig][LHSCase]]
inferred pure: [x2=p; 4<=inf_425]

Entail  (18): Valid. 
<1>EXISTS(flted_62_445: true & flted_62_445=1 & x2=r & Anon_448=a & q_449=p & inf_flted_7_454+1=m & 3<=inf_flted_7_454 & {FLOW,(17,18)=__norm})
inferred heap: [q_449::ll<inf_flted_7_454>@M[Orig]]
inferred pure: [q_449=p; 3<=inf_flted_7_454]

Entail  (19): Valid. 
<1>true & m=n & 4<=n & {FLOW,(17,18)=__norm}
inferred pure: [4<=n]

Entail  (20): Valid. 
<1>EXISTS(q_491,flted_7_489: q_491::ll<flted_7_489>@M[Orig] & flted_7_489+1=n & n=1 & {FLOW,(17,18)=__norm})
inferred pure: [n!=0; n=1]

Entail  (21): Valid. 
<1>q::ll<m>@M[Orig][LHSCase] & m=0 & {FLOW,(17,18)=__norm}
inferred pure: [m=0]

Entail  (22): Valid. 
<1>true & q=null & {FLOW,(17,18)=__norm}

Entail  (23): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [q=null]

Entail  (24): Valid. 
<1>a::ll<m>@M[Orig][LHSCase] & Anon_24=Anon_23 & m=0 & {FLOW,(17,18)=__norm}
inferred pure: [m=0]

Entail  (25): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x=null]

Entail  (26): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (27): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x!=null]

Entail  (28): Valid. 
<1>false & false & {FLOW,(17,18)=__norm}
inferred pure: [x=null]

Entail  (29): Valid. 
<1>true & Anon_27=inf_Anon_556 & inf_flted_95_557=null & {FLOW,(17,18)=__norm}
inferred heap: [x::node<inf_Anon_556,inf_flted_95_557>@M[Orig]]
inferred pure: [inf_flted_95_557=null]

Stop Omega... 459 invocations 
