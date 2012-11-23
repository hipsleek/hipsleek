Starting Reduce... 
Starting Omega...oc
Entail (1): Valid. 

<1>true & Term[1,Anon_11] & {FLOW,(17,18)=__norm}

Entail (2): Fail. 
<1>: _0_0: Error: The variance is not well-founded (not decreasing).

<1>true & Fail_May[0,Anon_12] & {FLOW,(17,18)=__norm}

Entail (3): Fail. 
<1>: _0_0: Error: Term->MayLoop transition is invalid.

<1>true & Fail_May[Anon_15] & {FLOW,(17,18)=__norm}

Entail (4): Fail. 
<1>: _0_0: Error: Term->Loop transition is invalid.

<1>true & Fail_Must[Anon_16] & {FLOW,(17,18)=__norm}

Entail (5): Valid. 

<1>true & Loop & {FLOW,(17,18)=__norm}

Entail (6): Valid. 

<1>true & Loop & {FLOW,(17,18)=__norm}

Entail (7): Valid. 

<1>true & Loop & {FLOW,(17,18)=__norm}

Entail (8): Valid. 

<1>true & MayLoop & {FLOW,(17,18)=__norm}

Entail (9): Valid. 

<1>true & MayLoop & {FLOW,(17,18)=__norm}

Entail (10): Valid. 

<1>true & MayLoop & {FLOW,(17,18)=__norm}

Entail (11): Valid. 

<1>true & Term[n] & n=2+m & {FLOW,(17,18)=__norm}

Entail (12): Fail. 
<1>: _0_0: Error: Term->Loop transition is invalid.

<1>
   true & Term[x] & 0<(n+3) & 0<=n & {FLOW,(17,18)=__norm}
   or true & Fail_Must[x] & 0<(n+3) & n<0 & {FLOW,(17,18)=__norm}
   

Entail (13): Valid. 

<1>true & Term[x] & 0<=n & {FLOW,(17,18)=__norm}

Entail (14): Fail.(may) cause:ror[(failure_code=213)  0<=(n+3) |-  n<0 (may-bug).,(failure_code=213)  0<=(n+3) |-  0<=n (may-bug).]


Entail (15): Valid. 

<1>true & Term[x] & 5<n & {FLOW,(17,18)=__norm}

Entail (16): Fail.(may) cause:ror[(failure_code=213)  0<=(n+3) |-  n<0 (may-bug).,(failure_code=213)  0<=(n+3) |-  0<=n (may-bug).]


Entail (17): Valid. 
<1>: _0_0: Error: Term->Loop transition is invalid.

<1>true & Fail_Must[x] & 0<=(n+3) & {FLOW,(17,18)=__norm}
<2>true & Term[x] & 0<=(n+3) & {FLOW,(17,18)=__norm}

Entail (18): Valid. 

<1>
   true & Term[x] & {FLOW,(17,18)=__norm}
   or true & Loop & {FLOW,(17,18)=__norm}
   

Entail (19): Fail. 
<1>: _0_0: Error: Term->Loop transition is invalid.

<1>
   true & Fail_Must[x] & {FLOW,(17,18)=__norm}
   or true & Loop & {FLOW,(17,18)=__norm}
   

Entail (20): Valid. 
<2>: _0_0: Error: Term->Loop transition is invalid.

<1>true & Term[x] & {FLOW,(17,18)=__norm}
<2>true & Fail_Must[x] & {FLOW,(17,18)=__norm}

Entail (21): Valid. 

<1>true & Loop & {FLOW,(17,18)=__norm}
<2>true & Loop & {FLOW,(17,18)=__norm}

Entail (22): Valid. 
<3>: _0_0: Error: Term->Loop transition is invalid.
<4>: _0_0: Error: Term->Loop transition is invalid.

<1>
   true & Term[x] & {FLOW,(17,18)=__norm}
   or true & Loop & {FLOW,(17,18)=__norm}
   
<2>
   true & Term[x] & {FLOW,(17,18)=__norm}
   or true & Loop & {FLOW,(17,18)=__norm}
   
<3>
   true & Fail_Must[x] & {FLOW,(17,18)=__norm}
   or true & Loop & {FLOW,(17,18)=__norm}
   
<4>
   true & Fail_Must[x] & {FLOW,(17,18)=__norm}
   or true & Loop & {FLOW,(17,18)=__norm}
   

Entail (23): Fail. 
<1>: _0_0: Error: The variance is not well-founded (not decreasing).

<1>
   true & Term[x] & {FLOW,(17,18)=__norm}
   or true & Fail_May[x - 1] & {FLOW,(17,18)=__norm}
   

Entail (24): Fail. 
<1>: _0_0: Error: Term->Loop transition is invalid.
 _0_0: Error: Term->Loop transition is invalid.

<1>
   true & Fail_Must[x] & {FLOW,(17,18)=__norm}
   or true & Fail_Must[x - 1] & {FLOW,(17,18)=__norm}
   

Entail (25): Fail. 
<1>: _0_0: Error: The variance is not well-founded (not decreasing).
<2>: _0_0: Error: Term->Loop transition is invalid.
<3>: _0_0: Error: Term->Loop transition is invalid.
 _0_0: Error: The variance is not well-founded (not decreasing).
<4>: _0_0: Error: Term->Loop transition is invalid.
 _0_0: Error: Term->Loop transition is invalid.

<1>
   true & Term[x] & {FLOW,(17,18)=__norm}
   or true & Fail_May[x - 1] & {FLOW,(17,18)=__norm}
   
<2>
   true & Term[x] & {FLOW,(17,18)=__norm}
   or true & Fail_Must[x - 1] & {FLOW,(17,18)=__norm}
   
<3>
   true & Fail_Must[x] & {FLOW,(17,18)=__norm}
   or true & Fail_May[x - 1] & {FLOW,(17,18)=__norm}
   
<4>
   true & Fail_Must[x] & {FLOW,(17,18)=__norm}
   or true & Fail_Must[x - 1] & {FLOW,(17,18)=__norm}
   

Entail (26): Fail. 
<1>: _0_0: Error: The variance is not well-founded (not decreasing).

<1>true & Fail_May[x] & {FLOW,(17,18)=__norm}

Entail (27): Fail. 
<1>: _0_0: Error: The variance is not well-founded (not decreasing).

<1>true & Fail_May[x] & {FLOW,(17,18)=__norm}

Stop Omega... 34 invocations 
