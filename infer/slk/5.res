Starting Omega...oc

Entail (1) : Valid. 

 <1>EXISTS(q_52,flted_7_50: q_52::ll<flted_7_50>@M[Orig]&flted_7_50+1=n & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; n!=0 | y!=null]


Entail (2) : Valid. 

 <1>EXISTS(q_84,flted_7_82: q_84::ll<flted_7_82>@M[Orig]&flted_7_82+1=n & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; n!=0]


Entail (3) : Valid. 

 <1>EXISTS(flted_7_106: b::ll<flted_7_106>@M[Orig]&flted_7_106+1=n&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


Entail (4) : Valid. 

 <1>emp&y=null & n=0&{FLOW,(19,20)=__norm}[]


Entail (5) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=1]


Entail (6) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n!=1]


Entail (7) : Valid. 

 <1>emp&0<n & m<n & 4<=n&{FLOW,(19,20)=__norm}[]
 inferred pure: [4<=n]


Entail (8) : Valid. 

 <1>emp&0<n & m<n & 4<m & 9<=n&{FLOW,(19,20)=__norm}[]
 inferred pure: [9<=n]


Entail (9) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n<=0]


Entail (10) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [n<=m | n<=0]


Entail (11) : Fail.(must) cause: true |-  n=2 & n=1. LOCS:[0;112] (RHS: contradiction)


Entail (12) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [m!=2 | n<=0]


Entail (13) : Fail.(may) cause: 2<m |-  m<a. LOCS:[0;133] (may-bug)


Entail (14) : Fail.(may) cause:AndR[ 2<m |-  4<m. LOCS:[138];  2<m |-  m<p. LOCS:[138] (may-bug).]


Entail (15) : Fail.(may) cause:AndR[ 2<m |-  4<m. LOCS:[143];  2<m |-  m<p. LOCS:[143] (may-bug).]


Entail (16) : Valid. 

 <1>emp&2<m & 5<=m & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [(1+m)<=p; 5<=m]

Stop Omega... 116 invocations 
