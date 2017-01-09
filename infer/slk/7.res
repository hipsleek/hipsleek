Starting Omega...oc

Entail (1) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [1>n]


!!! dumping for sleek_dump(fail)
Entail (2) : Fail.


Entail (3) : Valid. 

 <1>emp&2<m & a=p & b=q & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [m<p]


!!! dumping for sleek_dump(fail)
Entail (4) : Fail.


!!! dumping for sleek_dump(fail)
Entail (5) : Fail.


Entail (6) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [3>m]


Entail (7) : Valid. 

 <1>emp&2<m & m=p & 5<=m&{FLOW,(19,20)=__norm}[]
 inferred pure: [5<=m]


Entail (8) : Valid. 

 <1>emp&2<m & 5<=m & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [m<p; 5<=m]


Entail (9) : Valid. 

 <1>emp&6<m & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [m<p]


!!! dumping for sleek_dump(fail)
Entail (10) : Fail.


!!! dumping for sleek_dump(fail)
Entail (11) : Fail.


Entail (12) : Valid. 

 <1>emp&6<m & 6<=p&{FLOW,(19,20)=__norm}[]
 inferred pure: [6<=p]


!!! dumping for sleek_dump(fail)
Entail (13) : Fail.


!!! dumping for sleek_dump(fail)
Entail (14) : Fail.


!!! dumping for sleek_dump(fail)
Entail (15) : Fail.


Entail (16) : Valid. 

 <1>(exists flted_7_125: b::ll<flted_7_125>@M&n=flted_7_125+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [x!=null]


Entail (17) : Valid. 

 <1>(exists flted_7_144: b::ll<flted_7_144>@M&n=flted_7_144+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


Entail (18) : Valid. 

 <1>(exists flted_7_163: b::ll<flted_7_163>@M&n=flted_7_163+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [(n!=0 | x!=null)]

Stop Omega... 186 invocations 
SAT Count   : 111
SAT % Hit   : 53.15%
IMPLY Count : 93
IMPLY % Hit : 53.76%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.08488,333)
Total verification time: 0.15 second(s)
	Time spent in main process: 0.1 second(s)
	Time spent in child processes: 0.05 second(s)

