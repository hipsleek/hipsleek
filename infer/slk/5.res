Starting Omega...oc

Entail (1) : Valid. 

 <1>(exists q_49,flted_7_47: q_49::ll<flted_7_47>@M&n=flted_7_47+1 & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; (n!=0 | y!=null)]


Entail (2) : Valid. 

 <1>(exists q_77,flted_7_75: q_77::ll<flted_7_75>@M&n=flted_7_75+1 & n=1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n=1; n!=0]


Entail (3) : Valid. 

 <1>(exists flted_7_99: b::ll<flted_7_99>@M&n=flted_7_99+1&{FLOW,(19,20)=__norm})[]
 inferred pure: [n!=0]


Entail (4) : Valid. 

 <1>emp&y=null & n=0&{FLOW,(19,20)=__norm}[]
 inferred pure: [n=0]


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
 inferred pure: [1>n]


Entail (10) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [(m>=n | 1>n)]


!!! dumping for sleek_dump(fail)
Entail (11) : Fail.


Entail (12) : Valid. 

 <1>hfalse&false&{FLOW,(19,20)=__norm}[]
 inferred pure: [(m!=2 | 1>n)]


!!! dumping for sleek_dump(fail)
Entail (13) : Fail.


!!! dumping for sleek_dump(fail)
Entail (14) : Fail.


!!! dumping for sleek_dump(fail)
Entail (15) : Fail.


Entail (16) : Valid. 

 <1>emp&2<m & 5<=m & m<p&{FLOW,(19,20)=__norm}[]
 inferred pure: [m<p; 5<=m]

Stop Omega... 148 invocations 
SAT Count   : 98
SAT % Hit   : 59.18%
IMPLY Count : 74
IMPLY % Hit : 54.05%
Time(cache overhead) : 0. (seconds)

!!! log(small):(0.057037,279)
Total verification time: 0.13 second(s)
	Time spent in main process: 0.09 second(s)
	Time spent in child processes: 0.04 second(s)

