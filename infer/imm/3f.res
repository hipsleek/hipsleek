Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>true&a=Anon_11 & b=q & Anon_13=Anon_12 & Anon_14=r & v1<=1 & v1<=v2&{FLOW,(17,18)=__norm}
inferred pure: [v1<=v2; v1<=1]

Entail  (2): Valid. 

<1>true&a=Anon_15 & b=q & v1<:v2 & Anon_17=Anon_16 & Anon_18=r & v1<=1&{FLOW,(17,18)=__norm}
inferred pure: [v1<=1]

Entail  (3): Valid. 

<1>true&a=Anon_19 & b=q & 2<=v2&{FLOW,(17,18)=__norm}
inferred pure: [2<=v2]

Entail  (4): Valid. 

<1>true&v2<:@L & a=Anon_20 & b=q & Anon_22=Anon_21 & Anon_23=r & 2<=v2&{FLOW,(17,18)=__norm}
inferred pure: [2<=v2]

Entail  (5): Fail.(may) cause:(failure_code=213)  true |-  v1<:v2;  true |-  v1<:@I (may-bug).


Entail  (6): Fail.(may) cause:(failure_code=213)  true |-  v1<:@I (may-bug).


Entail  (7): Valid. 

<1>true&a=Anon_29 & b=r & 2<=v2&{FLOW,(17,18)=__norm}
inferred pure: [2<=v2]

Entail  (8): Fail.(may) cause:(failure_code=213)  true |-  b=d (may-bug).


Entail  (9): Valid. 

<1>true&c=a & b=d&{FLOW,(17,18)=__norm}
inferred pure: [b=d]

Stop Omega... 103 invocations 
