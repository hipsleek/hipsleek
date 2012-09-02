Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&A(n,m,z)&{FLOW,(19,20)=__norm}[]


Entail (2) : Valid. 

 <1>emp&n=1 & Anon_40=Anon_12 & q_41=y & m+1=z&{FLOW,(19,20)=__norm}[]
 inferred rel: [RELDEFN A: ( n=1 & z=m+1 & 0<=m) -->  A(n,m,z)]


Entail (3) : Valid. 

 <1>emp&y!=null & A(n1,m,z1) & n=1+n1 & 1<=n & Anon_61=Anon_13 & q_62=y & z1+1=z&{FLOW,(19,20)=__norm}[]
 inferred rel: [RELDEFN A: ( n1=n-1 & z1=z-1 & 2<=z & 1<=n & A(n1,m,z1)) -->  A(n,m,z)]

Stop Omega... 34 invocations 
