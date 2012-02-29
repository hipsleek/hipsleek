Starting Reduce... 
Starting Omega...oc
Entail  (1): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [n<=0]

Entail  (2): Fail.(may) cause:(failure_code=213)  2<m & a=p |-  m<a (may-bug).


Entail  (3): Fail.(may) cause:(failure_code=213)  2<m & a=p |-  m<a (may-bug).


Entail  (4): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).


Entail  (5): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).


Entail  (6): Valid. 

<1>false&false&{FLOW,(17,18)=__norm}
inferred pure: [m<=2]

Entail  (7): Fail.(may) cause:(failure_code=213)  2<m & m=p |-  4<m (may-bug).


Entail  (8): Fail.(may) cause:(failure_code=213)  2<m |-  4<m;  2<m |-  m<p (may-bug).


Entail  (9): Fail.(may) cause:(failure_code=213)  6<m |-  m<p (may-bug).


Entail  (10): Fail.(may) cause:(failure_code=213)  6<m |-  m<p (may-bug).


Entail  (11): Fail.(may) cause:(failure_code=213)  6<m |-  5<p;  6<m |-  m<p (may-bug).


Entail  (12): Valid. 

<1>true&6<m & 6<=p&{FLOW,(17,18)=__norm}
inferred pure: [6<=p]

Entail  (13): Fail.(may) cause:(failure_code=213)  6<m |-  z<m;  6<m |-  m<p (may-bug).


Entail  (14): Fail.(may) cause:(failure_code=213)  n!=0 & (q=null & inf_n_124=0 | q!=null & 1<=inf_n_124) |-  inf_n_124=n (may-bug).


Entail  (15): Fail.(must) cause:(failure_code=213)  n<0 & 0<=inf_n_141 |-  inf_n_141=n (must-bug).

<1>true&n<0 & inf_ann_140<=0&{FLOW,(1,2)=__Error}
inferred heap: [x::ll<inf_n_141>@inf_ann_140[Orig][LHSCase]]
inferred pure: [inf_ann_140<=0]

Entail  (16): Valid. 

<1>EXISTS(flted_7_163: b::ll<flted_7_163>@M[Orig]&flted_7_163+1=n&{FLOW,(17,18)=__norm})
inferred pure: [x!=null]

Entail  (17): Valid. 

<1>EXISTS(flted_7_182: b::ll<flted_7_182>@M[Orig]&flted_7_182+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0]

Entail  (18): Valid. 

<1>EXISTS(flted_7_201: b::ll<flted_7_201>@M[Orig]&flted_7_201+1=n&{FLOW,(17,18)=__norm})
inferred pure: [n!=0 | x!=null]

Stop Omega... 203 invocations 
