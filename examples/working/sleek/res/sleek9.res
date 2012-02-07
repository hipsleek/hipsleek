Starting Reduce... 
Starting Omega...oc
Entail (1): Valid. 
Entail (2): Fail.(may) cause:(failure_code=213)  r1=r_448 & (a_435!=0 & x!=null & 1<=a_435 | a_435=0 & x=r_448 & a_435=0) & 
n=11 & r2=r_476 & 0<=b_481 & 0<=n3 & 0<=n2 & 0<=b_481 & 0<=n3 & 0<=(b_481+
n3) & 0<=n1 & 0<=n2 & 0<=b_481 & 0<=n3 & 0<=(b_481+n3) & 0<=(b_481+n3+n2) & 
(a_463!=0 & r_448!=null & 1<=a_463 | a_463=0 & r_448=r_476 & a_463=0) & 
flted_28_406+1=n & flted_28_406=b_481+n3+n2+n1 & (b_481!=0 & r_493!=null & 
1<=b_481 | b_481=0 & r_493=r3 & b_481=0) & r3!=null & (a_480!=0 & 
r_476!=null & 1<=a_480 | a_480=0 & r_476=r_493 & a_480=0) |-  exists(n1:exists(n2:exists(n3:exists(b_481:0<=n1 & 0<=n2 & 0<=b_481 & 
0<=n3 & r_493=r3 & n3=2 & n2=4 & n1=3 & 0<=(n3+b_481) & flted_28_406=n1+n3+
b_481+n2 & 0<=(n2+b_481+n3))))) (may-bug).
Entail (3): Valid. 
Entail (4): Valid. 
<1>EXISTS(Anon_1754,flted_28_1753,flted_28_1752: p::node<Anon_1754,flted_28_1752>@M[Derv] & flted_28_1753+1=n & flted_28_1752=null & n=11 & r3=p & 0<=n3 & 0<=n2 & 0<=n1 & 0<=n3 & 0<=n2 & flted_28_1753=n3+n2+n1 & 0<=(n3+n2) & 0<=n1 & 0<=n3 & 0<=n2 & n3=3 & n2=4 & n1=3 & flted_28_1753=n3+n2+n1 & 0<=(n3+n2) & {FLOW,(17,18)=__norm})
<2>EXISTS(Anon_1754,flted_28_1753,flted_28_1752: r3::lseg<b_1827,p>@M[Derv] * p::node<Anon_1754,flted_28_1752>@M[Derv] & flted_28_1753+1=n & flted_28_1752=null & n=11 & 0<=b_1827 & 0<=n3 & 0<=n2 & 0<=b_1827 & 0<=n3 & 0<=(b_1827+n3) & 0<=n1 & 0<=n2 & 0<=b_1827 & 0<=n3 & 0<=(b_1827+n3) & flted_28_1753=b_1827+n3+n2+n1 & 0<=(b_1827+n3+n2) & 0<=n1 & 0<=n2 & 0<=b_1827 & 0<=n3 & n3=3 & n2=4 & n1=3 & 0<=(b_1827+n3) & flted_28_1753=b_1827+n3+n2+n1 & 0<=(b_1827+n3+n2) & {FLOW,(17,18)=__norm})

Stop Omega... 722 invocations 
