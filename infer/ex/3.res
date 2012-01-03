Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
Inferred Heap:[ y::node<inf_40,inf_41>@M[Orig], b::node<inf_42,inf_43>@M[Orig]]
Inferred Pure:[ b=inf_41]
<1>true & a=inf_40 & b=inf_41 & c=inf_42 & d=inf_43 &
{FLOW,(17,18)=__norm}


Entail  (2): Valid. 
Inferred Heap:[ y::node<inf_48,inf_49>@M[Orig]]
Inferred Pure:[]
<1>true & a=inf_48 & b=inf_49 &
{FLOW,(17,18)=__norm}


Entail  (3): Valid. 
Inferred Heap:[ y::ll<inf_53>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & n=inf_53 &
{FLOW,(17,18)=__norm}


Entail  (4): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Entail  (5): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (6): Valid. 
<1>true & n=0 & y=null &
{FLOW,(17,18)=__norm}


Entail  (7): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>true & y=null & n=0 &
{FLOW,(17,18)=__norm}


Entail  (8): Fail.(may) cause:15.4 no match for rhs data node: y (may-bug).

Entail  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=1]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (10): Valid. 
Inferred Heap:[ y::ll<inf_115>@M[Orig][LHSCase]]
Inferred Pure:[ inf_115=0]
<1>true & n=inf_115 & inf_115=0 &
{FLOW,(17,18)=__norm}


Entail  (11): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (12): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_150,flted_7_148: q_150::ll<flted_7_148>@M[Orig] & flted_7_148+
1=n & n=1 &
{FLOW,(17,18)=__norm})


Entail  (13): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_174: b::ll<flted_7_174>@M[Orig] & flted_7_174+1=n &
{FLOW,(17,18)=__norm})


Entail  (14): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>y::ll<n>@M[Orig][LHSCase] & n=0 &
{FLOW,(17,18)=__norm}


Entail  (15): Valid. 
Inferred Heap:[]
Inferred Pure:[ y=null]
<1>y::ll<n>@M[Orig][LHSCase] & y=null &
{FLOW,(17,18)=__norm}


Entail  (16): Valid. 
Inferred Heap:[]
Inferred Pure:[ y=null]
<1>y::ll<n>@M[Orig][LHSCase] & y=null &
{FLOW,(17,18)=__norm}


Entail  (17): Fail.(may) cause:(failure_code=213)  flted_7_211+1=n & (q_213=null & flted_7_211=0 | q_213!=null & 
1<=flted_7_211) |-  q_213=null (may-bug).

Entail  (18): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & y=null) & 0<=n, n=1]
<1>EXISTS(q_243,flted_7_241: q_243::ll<flted_7_241>@M[Orig] & flted_7_241+
1=n & n=1 &
{FLOW,(17,18)=__norm})


Entail  (19): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_273,flted_7_271: q_273::ll<flted_7_271>@M[Orig] & flted_7_271+
1=n & n=1 &
{FLOW,(17,18)=__norm})


Entail  (20): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (21): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>EXISTS(flted_7_303: b::ll<flted_7_303>@M[Orig] & flted_7_303+1=n &
{FLOW,(17,18)=__norm})


Entail  (22): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_330,flted_7_328: q_330::ll<flted_7_328>@M[Orig] & flted_7_328+
1=n & n=1 &
{FLOW,(17,18)=__norm})


Entail  (23): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>y::ll<n>@M[Orig][LHSCase] & n=0 &
{FLOW,(17,18)=__norm}


Entail  (24): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_358: b::ll<flted_7_358>@M[Orig] & flted_7_358+1=n &
{FLOW,(17,18)=__norm})


Entail  (25): Valid. 
Inferred Heap:[ y::node<inf_367,inf_368>@M[Orig], y::node<inf_Anon_369,inf_Anon_370>@M[Orig]]
Inferred Pure:[]
<1>true & a=inf_367 & b=inf_368 & Anon_21=inf_Anon_369 & 
Anon_22=inf_Anon_370 &
{FLOW,(17,18)=__norm}


Entail  (26): Valid. 
Inferred Heap:[ y::node<inf_376,inf_377>@M[Orig], y::ll<inf_378>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & a=inf_376 & b=inf_377 & m=inf_378 &
{FLOW,(17,18)=__norm}


Entail  (27): Valid. 
Inferred Heap:[ y::node<inf_389,inf_390>@M[Orig], b::ll<inf_m_391>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_390, inf_m_391=0 - 1]
<1>true & m+1=0 & a=inf_389 & b=inf_390 & inf_m_391=0 - 1 &
{FLOW,(17,18)=__norm}


Entail  (28): Valid. 
Inferred Heap:[ y::node<inf_409,inf_410>@M[Orig], b::ll<inf_m_411>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_410, inf_m_411=0 - 1]
<1>true & m+1=0 & a=inf_409 & b=inf_410 & inf_m_411=0 - 1 &
{FLOW,(17,18)=__norm}


Entail  (29): Valid. 
Inferred Heap:[ y::node<inf_428,inf_b_429>@M[Orig], b::ll<inf_431>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_429=b]
<1>true & a=inf_428 & m=inf_431 & inf_b_429=b &
{FLOW,(17,18)=__norm}


Entail  (30): Valid. 
Inferred Heap:[ y::node<inf_445,inf_b_446>@M[Orig], b::ll<inf_448>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_446=b]
<1>true & b!=null & a=inf_445 & m=inf_448 & inf_b_446=b &
{FLOW,(17,18)=__norm}


Stop Omega... 398 invocations 
