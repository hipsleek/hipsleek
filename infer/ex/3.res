Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid. 
Inferred Heap:[ y::node<inf_40,inf_41>@M[Orig], b::node<inf_42,inf_43>@M[Orig]]
Inferred Pure:[ b=inf_41]
<1>true & a=inf_40 & b=inf_41 & c=inf_42 & d=inf_43 &
{FLOW,(17,18)=__norm}


Infer  (2): Valid. 
Inferred Heap:[ y::node<inf_48,inf_49>@M[Orig]]
Inferred Pure:[]
<1>true & a=inf_48 & b=inf_49 &
{FLOW,(17,18)=__norm}


Infer  (3): Valid. 
Inferred Heap:[ y::ll<inf_56>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & n=inf_56 &
{FLOW,(17,18)=__norm}


Infer  (4): Fail.(may) cause:(failure_code=15.3)  true |-  y!=null (may-bug).

Infer  (5): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (6): Valid. 
<1>true & n=0 & y=null &
{FLOW,(17,18)=__norm}


Infer  (7): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>true & n=0 & y=null &
{FLOW,(17,18)=__norm}


Infer  (8): Fail.(may) cause:15.4 no match for rhs data node: y (may-bug).

Infer  (9): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=1]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (10): Valid. 
Inferred Heap:[ y::ll<inf_127>@M[Orig][LHSCase]]
Inferred Pure:[ inf_127=0]
<1>true & n=0 & inf_127=0 &
{FLOW,(17,18)=__norm}


Infer  (11): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (12): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_165,flted_7_163: q_165::ll<flted_7_163>@M[Orig] &
flted_7_163=0 & n=1 &
{FLOW,(17,18)=__norm})


Infer  (13): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_189: b::ll<flted_7_189>@M[Orig] & flted_7_189+1=n &
{FLOW,(17,18)=__norm})


Infer  (14): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>y::ll<n>@M[Orig][LHSCase] & n=0 &
{FLOW,(17,18)=__norm}


Infer  (15): Valid. 
Inferred Heap:[]
Inferred Pure:[ y=null]
<1>y::ll<n>@M[Orig][LHSCase] & y=null &
{FLOW,(17,18)=__norm}


Infer  (16): Valid. 
Inferred Heap:[]
Inferred Pure:[ y=null]
<1>y::ll<n>@M[Orig][LHSCase] & y=null &
{FLOW,(17,18)=__norm}


Infer  (17): Fail.(may) cause:(failure_code=213)  flted_7_226+1=n & (q_228=null & flted_7_226=0 | q_228!=null & 
1<=flted_7_226) |-  q_228=null (may-bug).

Infer  (18): Valid. 
Inferred Heap:[]
Inferred Pure:[ !(n=0 & y=null) & 0<=n, n=1]
<1>EXISTS(q_258,flted_7_256: q_258::ll<flted_7_256>@M[Orig] &
flted_7_256=0 & n=1 &
{FLOW,(17,18)=__norm})


Infer  (19): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_288,flted_7_286: q_288::ll<flted_7_286>@M[Orig] &
flted_7_286=0 & n=1 &
{FLOW,(17,18)=__norm})


Infer  (20): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (21): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>EXISTS(flted_7_318: b::ll<flted_7_318>@M[Orig] & flted_7_318+1=n &
{FLOW,(17,18)=__norm})


Infer  (22): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0, n=1]
<1>EXISTS(q_345,flted_7_343: q_345::ll<flted_7_343>@M[Orig] &
flted_7_343=0 & n=1 &
{FLOW,(17,18)=__norm})


Infer  (23): Valid. 
Inferred Heap:[]
Inferred Pure:[ n=0]
<1>y::ll<n>@M[Orig][LHSCase] & n=0 &
{FLOW,(17,18)=__norm}


Infer  (24): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>EXISTS(flted_7_373: b::ll<flted_7_373>@M[Orig] & flted_7_373+1=n &
{FLOW,(17,18)=__norm})


Infer  (25): Valid. 
Inferred Heap:[ y::node<inf_382,inf_383>@M[Orig], y::node<inf_Anon_384,inf_Anon_385>@M[Orig]]
Inferred Pure:[]
<1>true & a=inf_382 & b=inf_383 & Anon_21=inf_Anon_384 & 
Anon_22=inf_Anon_385 &
{FLOW,(17,18)=__norm}


Infer  (26): Valid. 
Inferred Heap:[ y::node<inf_391,inf_392>@M[Orig], y::ll<inf_396>@M[Orig][LHSCase]]
Inferred Pure:[]
<1>true & a=inf_391 & b=inf_392 & m=inf_396 &
{FLOW,(17,18)=__norm}


Infer  (27): Valid. 
Inferred Heap:[ y::node<inf_410,inf_411>@M[Orig], b::ll<inf_m_415>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_411, inf_m_415=0 - 1]
<1>true & m=0 - 1 & inf_410=a & inf_411=b & inf_m_415=0 - 1 &
{FLOW,(17,18)=__norm}


Infer  (28): Valid. 
Inferred Heap:[ y::node<inf_436,inf_437>@M[Orig], b::ll<inf_m_441>@M[Orig][LHSCase]]
Inferred Pure:[ b=inf_437, inf_m_441=0 - 1]
<1>true & m=0 - 1 & inf_436=a & inf_437=b & inf_m_441=0 - 1 &
{FLOW,(17,18)=__norm}


Infer  (29): Valid. 
Inferred Heap:[ y::node<inf_461,inf_b_462>@M[Orig], b::ll<inf_467>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_462=b]
<1>true & inf_461=a & inf_467=m & b=inf_b_462 &
{FLOW,(17,18)=__norm}


Infer  (30): Valid. 
Inferred Heap:[ y::node<inf_484,inf_b_485>@M[Orig], b::ll<inf_490>@M[Orig][LHSCase]]
Inferred Pure:[ inf_b_485=b]
<1>true & inf_484=a & inf_490=m & b=inf_b_485 & inf_b_485!=null &
{FLOW,(17,18)=__norm}


Halting Reduce... 
Stop Omega... 561 invocations 
