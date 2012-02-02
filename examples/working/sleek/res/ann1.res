Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 
<1>true & a=Anon_11 & b=Anon_12 & {FLOW,(17,18)=__norm}

Entail  (2): Valid. 
<1>EXISTS(v: true & a=Anon_13 & b=Anon_14 & w<:v & {FLOW,(17,18)=__norm})

Entail  (3): Valid. 
<1>true & w=v & a=Anon_15 & b=Anon_16 & {FLOW,(17,18)=__norm}

Entail  (4): Valid. 
Entail  (5): Valid. 
Entail  (6): Valid. 
Entail  (7): Valid. 
Entail  (8): Fail.(must) cause:(failure_code=213)  true |-  @I<:@M (RHS: contradiction).
Entail  (9): Fail.(must) cause:(failure_code=213)  true |-  @L<:@I (RHS: contradiction).
Entail  (10): Valid. 
Entail  (11): Valid. 
Entail  (12): Valid. 
Entail  (13): Valid. 
Entail  (14): Valid. 
Entail  (15): Valid. 
Entail  (16): Valid. 
Entail  (17): Fail.(may) cause:(failure_code=213)  true |-  v<:@I (may-bug).
Entail  (18): Valid. 
Entail  (19): Fail.(must) cause:(failure_code=213)  true |-  false (RHS: contradiction).
Entail  (20): Valid. 
Entail  (21): Fail.(may) cause:(failure_code=213)  w<:@I |-  w<:@M (may-bug).
Entail  (22): Fail.(may) cause:(failure_code=213)  w<:@L |-  w<:@I (may-bug).
Entail  (23): Valid. 
Entail  (24): Valid. 
Entail  (25): Valid. 
Stop Omega... 51 invocations 
