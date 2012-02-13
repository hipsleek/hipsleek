
Processing file "bt-insert.ss"
Parsing bt-insert.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure insert$node3... 
Inferred Heap:[]
Inferred Pure:[ n!=0 | h!=0, n!=0 | h!=0, n!=0 | h!=0, n!=0 | h!=0]

INF-POST-FLAG: true
REL :  A(n,h,m,k)
POST:  (h+1)>=k & k>=h & (k+n)>=(2+h) & k>=2 & n+1=m
PRE :  1<=h & 1<=n
OLD SPECS:  EInfer [A,n,h]
   EBase exists (Expl)(Impl)[n; h](ex)x::bt<n,h>@M[Orig][LHSCase]&true&
         {FLOW,(20,21)=__norm}
           EBase true&MayLoop&{FLOW,(1,23)=__flow}
                   EAssume 1::
                     EXISTS(m,k: x::bt<m,k>@M[Orig][LHSCase]&A(n,h,m,k)&
                     {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n; h](ex)x::bt<n,h>@M[Orig][LHSCase]&true&
       {FLOW,(20,21)=__norm}
         EBase true&1<=h & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                 EAssume 1::
                   x::bt<m,k>@M[Orig][LHSCase]&(h+1)>=k & k>=h & (k+n)>=(2+
                   h) & k>=2 & n+1=m & (k=2 | 3<=k) & 0<=n & 0<=h&
                   {FLOW,(20,21)=__norm}
NEW RELS: [ (k=2 & h=1 & n=1 & m=2 | h=k & m=n+1 & 2<=n & 2<=k) --> A(n,h,m,k), (k=h & m=n+1 & 2<=h & 2<=n) --> A(n,h,m,k), ((k=k_857+1 & m_856=(n_657-n)+m & h_658=h-1 & 0<=n_657 & n_657<=(n-2) & 
  n<(n_657+m) & 1<=k_857 & 2<=h | k=h & m_856=(n_657+m)-n & 1<=k_857 & 
  k_857<=(h-2) & 0<=n_657 & n_657<=(n-2) & 0<=h_658 & h_658<=(h-2) & 
  n<(n_657+m) | m_856=(n_657+m)-n & h_658=h-1 & 1<=k_857 & k_857<=(k-2) & 
  0<=n_657 & n_657<=(n-2) & k<=h & n<(n_657+m) | k=k_857+1 & m_856=(n_657+m)-
  n & 0<=n_657 & n_657<=(n-2) & (h_658+2)<=h & h<=(k_857+1) & n<(n_657+m) & 
  0<=h_658) & A(n_657,h_658,m_856,k_857)) --> A(n,h,m,k), ((k=k_897+1 & h_674=h-1 & m_896=(n_673+m)-n & 0<=n_673 & n_673<=(n-2) & 
  n<(n_673+m) & 2<=k_897 & 3<=h | k=k_897+1 & m_896=(n_673-n)+m & (h_674+
  1)<=h & 2<=h & h<=k_897 & 0<=n_673 & n_673<=(n-2) & 0<=h_674 & n<(n_673+
  m) | k=h & m_896=(n_673-n)+m & 0<=n_673 & n_673<=(n-2) & 1<=k_897 & 
  k_897<h & 0<=h_674 & h_674<h & n<(n_673+m) | h_674=h-1 & m_896=(n_673-n)+
  m & 1<=k_897 & k_897<k & k<h & 0<=n_673 & n_673<=(n-2) & n<(n_673+m)) & 
  A(n_673,h_674,m_896,k_897)) --> A(n,h,m,k)]

Procedure insert$node3 SUCCESS

Termination checking result:

Stop Omega... 515 invocations 
0 false contexts at: ()

Total verification time: 2.44 second(s)
	Time spent in main process: 1.27 second(s)
	Time spent in child processes: 1.17 second(s)
