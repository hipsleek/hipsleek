Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid.
Inferred Heap:[ y::node<inf_27,inf_28>[Orig]]
Inferred Pure:[]
<1>true & a=inf_27 & b=inf_28 &
{FLOW,(17,18)=__norm}


Infer  (2): Valid.
Inferred Heap:[ y::ll<inf_34>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & n=inf_34 &
{FLOW,(17,18)=__norm}


Infer  (3): Valid.
Inferred Heap:[ y::node<inf_43,inf_44>[Orig], b::node<inf_45,inf_46>[Orig]]
Inferred Pure:[ b=inf_44]
<1>true & a=inf_43 & b=inf_44 & c=inf_45 & d=inf_46 &
{FLOW,(17,18)=__norm}


Infer  (4): Valid.
Inferred Heap:[ y::node<inf_51,inf_52>[Orig], b::ll<inf_56>[Orig][LHSCase]]
Inferred Pure:[ b=inf_52]
<1>true & a=inf_51 & b=inf_52 & m=inf_56 &
{FLOW,(17,18)=__norm}


Infer  (5): Valid.
Inferred Heap:[ y::ll<inf_65>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_65 &
{FLOW,(17,18)=__norm}


Infer  (6): Valid.
Inferred Heap:[ y::ll<inf_n_78>[Orig][LHSCase]]
Inferred Pure:[ inf_n_78=0]
<1>true & n=0 & y=x & inf_n_78=0 &
{FLOW,(17,18)=__norm}


Infer  (7): Valid.
Inferred Heap:[ x::ll<inf_88>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_88 &
{FLOW,(17,18)=__norm}


Infer  (8): Valid.
Inferred Heap:[ y::ll<inf_97>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_97 &
{FLOW,(17,18)=__norm}


Infer  (9): Valid.
<1>true & a=ia & b=ib &
{FLOW,(17,18)=__norm}


Infer  (10): Valid.
Inferred Heap:[ y::node<inf_a_116,inf_flted_37_117>[Orig]]
Inferred Pure:[ inf_flted_37_117=null & 1<=inf_a_116]
<1>true & inf_flted_37_117=null & 1<=inf_a_116 &
{FLOW,(17,18)=__norm}


Infer  (11): Valid.
Inferred Heap:[]
Inferred Pure:[ 1<=aa]
<1>EXISTS(flted_40_133: true & flted_40_133=null & 1<=aa &
{FLOW,(17,18)=__norm})


Infer  (12): Valid.
<1>true & n=m &
{FLOW,(17,18)=__norm}


Infer  (13): Valid.
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (14): Valid.
Inferred Heap:[]
Inferred Pure:[ y!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Halting Reduce... 
Stop Omega... 172 invocations 
