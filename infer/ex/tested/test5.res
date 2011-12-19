Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
Inferred Heap:[]
Inferred Pure:[ x!=null]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (2): Valid. 
Inferred Heap:[]
Inferred Pure:[ n!=0]
<1>false & false &
{FLOW,(17,18)=__norm}


Entail  (3): Fail.(may) cause:(failure_code=213)  true |-  inf_b_73=b (may-bug).

Entail  (4): Valid. 
Inferred Heap:[ x::node<inf_Anon_117,inf_b_118>@M[Orig], y::node<inf_Anon_120,inf_flted_29_121>@M[Orig]]
Inferred Pure:[ inf_b_118=b & inf_flted_29_121=null]
<1>EXISTS(flted_29_112: true & Anon_18=1 & flted_29_112=1 & 
inf_Anon_117=Anon_17 & inf_Anon_120=Anon_19 & b=inf_b_118 & 
inf_flted_29_121=null &
{FLOW,(17,18)=__norm})



ERROR: at _0_0 
Message: y is not found in both sides
 exception in Entail  (5) check
: no residue 
Stop Omega... 94 invocations 
