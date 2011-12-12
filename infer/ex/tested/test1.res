Starting Reduce... 
Starting Omega...oc
Infer  (1): Valid.
Inferred Heap:[ y::node<inf_27,inf_28>[Orig]]
Inferred Pure:[]
<1>true & a=inf_27 & b=inf_28 &
{FLOW,(17,18)=__norm}


Infer  (2): Valid.
Inferred Heap:[ y::node<inf_36,inf_flted_13_37>[Orig]]
Inferred Pure:[ a=inf_36 & inf_flted_13_37=null]
<1>true & inf_36=a & inf_flted_13_37=null &
{FLOW,(17,18)=__norm}


Infer  (3): Valid.
Inferred Heap:[ y::ll<inf_44>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & n=inf_44 &
{FLOW,(17,18)=__norm}


Infer  (4): Valid.
Inferred Heap:[ y::node<inf_53,inf_54>[Orig], b::node<inf_55,inf_56>[Orig]]
Inferred Pure:[ b=inf_54]
<1>true & a=inf_53 & b=inf_54 & c=inf_55 & d=inf_56 &
{FLOW,(17,18)=__norm}


Infer  (5): Valid.
Inferred Heap:[ y::node<inf_61,inf_62>[Orig], y::ll<inf_66>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & a=inf_61 & b=inf_62 & m=inf_66 &
{FLOW,(17,18)=__norm}


Infer  (6): Valid.
Inferred Heap:[ y::node<inf_74,inf_75>[Orig], b::ll<inf_79>[Orig][LHSCase]]
Inferred Pure:[ b=inf_75]
<1>true & a=inf_74 & b=inf_75 & m=inf_79 &
{FLOW,(17,18)=__norm}


Infer  (7): Valid.
Inferred Heap:[ y::ll<inf_88>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_88 &
{FLOW,(17,18)=__norm}


Infer  (8): Valid.
Inferred Heap:[ y::ll<inf_n_101>[Orig][LHSCase]]
Inferred Pure:[ inf_n_101=0]
<1>true & n=0 & y=x & inf_n_101=0 &
{FLOW,(17,18)=__norm}


Infer  (9): Valid.
Inferred Heap:[ x::ll<inf_111>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_111 &
{FLOW,(17,18)=__norm}


Infer  (10): Valid.
Inferred Heap:[ y::ll<inf_120>[Orig][LHSCase]]
Inferred Pure:[]
<1>true & x=y & n=inf_120 &
{FLOW,(17,18)=__norm}


Infer  (11): Valid.
<1>true & a=ia & b=ib &
{FLOW,(17,18)=__norm}


Infer  (12): Valid.
Inferred Heap:[ y::node<inf_a_139,inf_flted_43_140>[Orig]]
Inferred Pure:[ inf_flted_43_140=null & 1<=inf_a_139]
<1>true & inf_flted_43_140=null & 1<=inf_a_139 &
{FLOW,(17,18)=__norm}


Infer  (13): Valid.
Inferred Heap:[]
Inferred Pure:[ 1<=aa]
<1>EXISTS(flted_46_156: true & flted_46_156=null & 1<=aa &
{FLOW,(17,18)=__norm})


Infer  (14): Valid.
Inferred Heap:[]
Inferred Pure:[ aa=a & 1<=a]
<1>EXISTS(flted_49_173: true & a=aa & flted_49_173=null & 1<=aa &
{FLOW,(17,18)=__norm})


Infer  (15): Valid.
<1>true & n=m &
{FLOW,(17,18)=__norm}


Infer  (16): Valid.
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Infer  (17): Valid.
Inferred Heap:[]
Inferred Pure:[ y!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Halting Reduce... 
Stop Omega... 221 invocations 
