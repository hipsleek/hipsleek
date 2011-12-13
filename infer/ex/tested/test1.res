Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid.
Inferred Heap:[ y::node<inf_28,inf_29>[Orig]]
Inferred Pure:[]
<1>true & a=inf_28 & b=inf_29 &
{FLOW,(17,18)=__norm}


Infer  (2): Valid.
Inferred Heap:[ y::ll<inf_36>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & n=inf_36 &
{FLOW,(17,18)=__norm}


Infer  (3): Valid.
Inferred Heap:[ y::node<inf_46,inf_47>[Orig], b::node<inf_48,inf_49>[Orig]]
Inferred Pure:[ b=inf_47]
<1>true & a=inf_46 & b=inf_47 & c=inf_48 & d=inf_49 &
{FLOW,(17,18)=__norm}


Infer  (4): Valid.
Inferred Heap:[ y::node<inf_55,inf_56>[Orig], b::ll<inf_60>[Orig][LHSCase]]
Inferred Pure:[ b=inf_56]
<1>true & a=inf_55 & b=inf_56 & m=inf_60 &
{FLOW,(17,18)=__norm}


Infer  (5): Valid.
Inferred Heap:[ y::ll<inf_70>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_70 &
{FLOW,(17,18)=__norm}


Infer  (6): Valid.
Inferred Heap:[ y::ll<inf_n_84>[Orig][LHSCase]]
Inferred Pure:[ inf_n_84=0]
<1>true & n=0 & y=x & inf_n_84=0 &
{FLOW,(17,18)=__norm}


Infer  (7): Valid.
Inferred Heap:[ x::ll<inf_95>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_95 &
{FLOW,(17,18)=__norm}


Infer  (8): Valid.
<1>true & a=ia & b=ib &
{FLOW,(17,18)=__norm}


Infer  (9): Valid.
Inferred Heap:[ y::node<inf_a_116,inf_flted_43_117>[Orig]]
Inferred Pure:[ inf_flted_43_117=null & 1<=inf_a_116]
<1>true & inf_flted_43_117=null & 1<=inf_a_116 &
{FLOW,(17,18)=__norm}


Infer  (10): Valid.
Inferred Heap:[]
Inferred Pure:[ 1<=aa]
<1>EXISTS(flted_47_134: true & flted_47_134=null & 1<=aa &
{FLOW,(17,18)=__norm})


Infer  (11): Valid.
<1>true & n=m &
{FLOW,(17,18)=__norm}


Infer  (12): Valid.
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (13): Valid.
Inferred Heap:[]
Inferred Pure:[ y!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Halting Reduce... 
Stop Omega... 164 invocations 
