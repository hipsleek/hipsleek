Starting Reduce... 
Starting Omega...oc

Entail (1): Valid. 

Entail (2): Valid. 
 <1>true & @zero[v1,v2,x1] & {FLOW,(17,18)=__norm}[][[empty]]


Entail (3): Fail.(may) cause:variable permission mismatch 321

Entail (4): Valid. 
 <1>true & @zero[v1,v2,x1] & v1=x1 & {FLOW,(17,18)=__norm}[][[empty]]


Entail (5): Valid. 
 <1>true & @zero[v1,v2] & {FLOW,(17,18)=__norm}[][[empty]]


Entail (6): Fail.(may) cause:variable permission mismatch 321

Entail (7): Fail.(may) cause:variable permission mismatch 321

Entail (8): Fail.(may) cause:variable permission mismatch 321

Entail (9): Valid. 
 <1>true & @zero[v1,v2] & {FLOW,(17,18)=__norm}[][[empty]]
<2>true & @zero[v1,v2] & {FLOW,(17,18)=__norm}[][[empty]]


Entail (10): Valid. 
 <1>true & @zero[v1,v2] & {FLOW,(17,18)=__norm}[][[empty]]


Entail (11): Valid. 
 <1>
    true & @zero[v1,v2] & {FLOW,(17,18)=__norm}[]
    or true & @zero[v2] & {FLOW,(17,18)=__norm}[]
    [[||OR|| ==> ]]


Entail (12): Valid. 
 <1>true & @zero[x,y] & {FLOW,(17,18)=__norm}
AND  <thread=id>  <ref:> true & @full[x] & x'=1+x[[empty]]


Entail (13): Valid. 
 <1>true & @zero[x] & 1+x=1+i & y'=1+y & id=z & {FLOW,(17,18)=__norm}[][[empty]]


Entail (14): Fail.(may) cause:variable permission mismatch 321
 
Halting Reduce... 
Stop Omega... 15 invocations 
