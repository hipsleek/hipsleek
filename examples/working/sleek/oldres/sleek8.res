Starting Omega...oc

Entail (1) : Valid. 


Entail (2) : Valid. 


Entail (3) : Valid. 


Entail (4) : Valid. 


Entail (5) : Valid. 


Entail (6) : Valid. 


Entail (7) : Valid. 


Entail (8) : Valid. 


Entail (9) : Valid. 


Entail (10) : Fail.(may) cause:UnionR[ 9<n |-  11<=n. LOCS:[63;1] (may-bug), 9<n |-  exists(b_1265:exists(n2:0<=b_1265 & 0<=n2 & 2<=n2 & (n2+9+b_1265)<=n & 
0<=(n2+b_1265))). LOCS:[63;0] (may-bug)]


Entail (11) : Valid. 


Entail (12) : Valid. 


Entail (13) : Valid. 


Entail (14) : Valid. 


Entail (15) : Fail.(must) cause:UnionR[UnionR[AndR[ true |-  n2=0 & n2=5. LOCS:[0;10;83] (RHS: contradiction), 0<=7 & n1=7 |-  n1=3. LOCS:[14;0;83] (must-bug)], n=7 |-  n=3+5. LOCS:[83;16] (must-bug)], n=7 |-  exists(b_1948:exists(n2:0<=b_1948 & 0<=n2 & n2=5 & 0<=(n2+b_1948) & 0<=3 & 
n=3+b_1948+n2)). LOCS:[83;0] (must-bug)]


Entail (16) : Valid. 


Entail (17) : Fail.(may) cause: (x!=null & 1<=a_2128 | a_2128=0 & x=r1 & a_2128=0) & 0<=b_2146 & 
(r1!=null & 1<=a_2145 | a_2145=0 & r1=r_2158 & a_2145=0) & (r_2158!=null & 
1<=b_2146 | b_2146=0 & r_2158=p & b_2146=0) & n=7 |-  exists(b_2146:exists(n2:0<=b_2146 & 0<=n2 & r_2158=p & n2=3 & 0<=(n2+
b_2146) & 0<=3 & n=3+b_2146+n2)). LOCS:[16;1;10;91;0] (may-bug)

Stop Omega... 378 invocations 
