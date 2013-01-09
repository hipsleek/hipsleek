Starting Omega...oc

Entail (1) : Valid. 

 <1>emp&A(n,m,z)&{FLOW,(19,20)=__norm}[]
 inferred rel: [RELDEFN A: ( true) -->  A(n,m,z)]


Entail (2) : Valid. 

 <1>emp&n=1 & Anon_12=Anon_40 & q_41=y & z=m+1&{FLOW,(19,20)=__norm}[]
 inferred rel: [RELDEFN A: ( n=1 & z=m+1 & 0<=m) -->  A(n,m,z)]


Entail (3) : Valid. 

 <1>emp&y!=null & A(n1,m,z1) & n=1+n1 & 1<=n & Anon_13=Anon_61 & q_62=y & z=z1+1&{FLOW,(19,20)=__norm}[]
 inferred rel: [RELDEFN A: ( n1=n-1 & z1=z-1 & 1<=n & 2<=z & A(n1,m,z1)) -->  A(n,m,z)]

Stop Omega... 42 invocations 
