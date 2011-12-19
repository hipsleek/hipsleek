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
Inferred Heap:[ y::ll<inf_55>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & n=inf_55 &
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
Inferred Heap:[ y::ll<inf_118>@M[Orig][LHSCase]]
Inferred Pure:[ inf_118=0]
<1>true & n=inf_118 & inf_118=0 &
{FLOW,(17,18)=__norm}


Entail  (11): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (12): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_155,flted_7_153: q_155::ll<flted_7_153>@M[Orig] & flted_7_153+
1=n & n=1 &
{FLOW,(17,18)=__norm})


Entail  (13): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_179: b::ll<flted_7_179>@M[Orig] & flted_7_179+1=n &
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


Entail  (17): Fail.(may) cause:(failure_code=213)  flted_7_216+1=n & (q_218=null & flted_7_216=0 | q_218!=null & 
1<=flted_7_216) |-  q_218=null (may-bug).

Entail  (18): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & y=null) & 0<=n, n=1]
<1>EXISTS(q_248,flted_7_246: q_248::ll<flted_7_246>@M[Orig] & flted_7_246+
1=n & n=1 &
{FLOW,(17,18)=__norm})


Entail  (19): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_278,flted_7_276: q_278::ll<flted_7_276>@M[Orig] & flted_7_276+
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
<1>EXISTS(flted_7_308: b::ll<flted_7_308>@M[Orig] & flted_7_308+1=n &
{FLOW,(17,18)=__norm})


Entail  (22): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_335,flted_7_333: q_335::ll<flted_7_333>@M[Orig] & flted_7_333+
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
<1>EXISTS(flted_7_363: b::ll<flted_7_363>@M[Orig] & flted_7_363+1=n &
{FLOW,(17,18)=__norm})


Entail  (25): Valid. 
Inferred Heap:[ y::node<inf_372,inf_373>@M[Orig], y::node<inf_Anon_374,inf_Anon_375>@M[Orig]]
Inferred Pure:[]
<1>true & a=inf_372 & b=inf_373 & Anon_21=inf_Anon_374 & 
Anon_22=inf_Anon_375 &
{FLOW,(17,18)=__norm}


Entail  (26): Valid. 
Inferred Heap:[ y::node<inf_381,inf_382>@M[Orig], y::ll<inf_385>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & a=inf_381 & b=inf_382 & m=inf_385 &
{FLOW,(17,18)=__norm}


Entail  (27): Valid. 
Inferred Heap:[ y::node<inf_398,inf_399>@M[Orig], b::ll<inf_m_402>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_399, inf_m_402=0 - 1]
<1>true & m+1=0 & a=inf_398 & b=inf_399 & inf_m_402=0 - 1 &
{FLOW,(17,18)=__norm}


Entail  (28): Valid. 
Inferred Heap:[ y::node<inf_422,inf_423>@M[Orig], b::ll<inf_m_426>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_423, inf_m_426=0 - 1]
<1>true & m+1=0 & a=inf_422 & b=inf_423 & inf_m_426=0 - 1 &
{FLOW,(17,18)=__norm}


Entail  (29): Valid. 
Inferred Heap:[ y::node<inf_445,inf_b_446>@M[Orig], b::ll<inf_450>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_446=b]
<1>true & a=inf_445 & m=inf_450 & inf_b_446=b &
{FLOW,(17,18)=__norm}


Entail  (30): Valid. 
Inferred Heap:[ y::node<inf_466,inf_b_467>@M[Orig], b::ll<inf_471>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_467=b]
<1>true & b!=null & a=inf_466 & m=inf_471 & inf_b_467=b &
{FLOW,(17,18)=__norm}


Stop Omega... 430 invocations 
