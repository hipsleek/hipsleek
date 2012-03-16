Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&b=Anon_12 & c=a & 1<=a&{FLOW,(17,18)=__norm}
inferred pure: [1<=a; c=a]

Entail  (2): Valid. 

<1>true&0<a & b=Anon_13 & a=c & 1<=c&{FLOW,(17,18)=__norm}
inferred pure: [1<=c; a=c]

Entail  (3): Valid. 

<1>EXISTS(flted_7_75: b::ll<flted_7_75>@M[Orig]&flted_7_75+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (4): Fail.(may) cause:(failure_code=213)  a=Anon_96 |-  0<a (may-bug).


Entail  (5): Fail.(may) cause:(failure_code=213)  0<a |-  Anon_120=a (may-bug).


Entail  (6): Valid. 

<1>true&0<b & a=b & Anon_15=Anon_14&{FLOW,(17,18)=__norm}

Entail  (7): Valid. 

<1>true&a=b & Anon_17=Anon_16 & 1<=b&{FLOW,(17,18)=__norm}
inferred pure: [1<=b]

Entail  (8): Valid. 

<1>true&2<b & a=b & Anon_19=Anon_18&{FLOW,(17,18)=__norm}

Entail  (9): Valid. 

<1>true&b=Anon_20 & 1<=a&{FLOW,(17,18)=__norm}
inferred pure: [1<=a]

Entail  (10): Valid. 

<1>true&0<a & a=c & 1<=c&{FLOW,(17,18)=__norm}
inferred pure: [1<=c; a=c]

Entail  (11): Valid. 

<1>true&c=a & 1<=a&{FLOW,(17,18)=__norm}
inferred pure: [1<=a; c=a]

Stop Omega... 116 invocations 
