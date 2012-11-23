Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n<=0]


Entail (2) : Fail.(may) cause: 2<m |-  m<a. LOCS:[0;19] (may-bug)


Entail (3) : Valid. 

 <1>emp&2<m & a=p & b=q & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [(1+m)<=p]


Entail (4) : Fail.(may) cause:AndR[ 2<m |-  4<m. LOCS:[29];  2<m |-  m<p. LOCS:[29] (may-bug).]


Entail (5) : Fail.(may) cause:AndR[ 2<m |-  4<m. LOCS:[34];  2<m |-  m<p. LOCS:[34] (may-bug).]


Entail (6) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [m<=2]


Entail (7) : Valid. 

 <1>emp&2<m & m=p & 5<=m&{FLOW,(19,20)=__norm}[]
 inferred pure: [5<=m]


Entail (8) : Valid. 

 <1>emp&2<m & 5<=m & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [(1+m)<=p; 5<=m]


Entail (9) : Valid. 

 <1>emp&6<m & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [(1+m)<=p]


Entail (10) : Fail.(may) cause: 6<m |-  m<p. LOCS:[61] (may-bug)


Entail (11) : Fail.(may) cause:AndR[ 6<m |-  5<p. LOCS:[67];  6<m |-  m<p. LOCS:[67] (may-bug).]


Entail (12) : Valid. 

 <1>emp&6<m & 6<=p&{FLOW,(19,20)=__norm}[]
 inferred pure: [6<=p]


Entail (13) : Fail.(may) cause:AndR[ 6<m |-  z<m. LOCS:[80];  6<m |-  m<p. LOCS:[80] (may-bug).]


Entail (14) : Fail.(may) cause: (q=null & inf_n_124=0 | q!=null & 1<=inf_n_124) & n!=0 |-  inf_n_124=n. LOCS:[6;1;87] (may-bug)


Entail (15) : Fail.(must) cause: 0<=inf_n_141 & n<0 |-  inf_n_141=n. LOCS:[8;91] (must-bug)


Entail (16) : Valid. 

 <1>EXISTS(flted_7_163: b::ll<flted_7_163>@M[Orig]&flted_7_163+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (17) : Valid. 

 <1>EXISTS(flted_7_182: b::ll<flted_7_182>@M[Orig]&flted_7_182+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


Entail (18) : Valid. 

 <1>EXISTS(flted_7_201: b::ll<flted_7_201>@M[Orig]&flted_7_201+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0 | x!=null]

Stop Omega... 196 invocations 
