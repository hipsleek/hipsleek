
Processing file "bt-insert.ss"
Parsing bt-insert.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node3... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0 | h!=0, n!=0 | h!=0, n!=0 | h!=0, n!=0 | h!=0]
!!! REL :  A(n,h,m,k)
!!! POST:  (h+1)>=k & k>=h & (k+n)>=(2+h) & k>=2 & n+1=m
!!! PRE :  1<=h & 1<=n
!!! OLD SPECS: ((None,[]),EInfer [A,n,h]
              EBase exists (Expl)(Impl)[n; h](ex)x::bt<n,h>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m,k: x::bt<m,k>@M[Orig][LHSCase]&
                                A(n,h,m,k)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h](ex)x::bt<n,h>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&1<=h & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(m_930,
                              k_931: x::bt<m_930,k_931>@M[Orig][LHSCase]&(h+
                              1)>=k_931 & k_931>=h & (k_931+n)>=(2+h) & 
                              k_931>=2 & n+1=m_930 & 0<=n & 0<=h&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (k=2 & n=1 & h=1 & m=2 | h=k & m=n+1 & 2<=n & 2<=k) --> A(n,h,m,k),
 (h=k & n=m-1 & 2<=k & 3<=m) --> A(n,h,m,k),
 ((k=k_857+1 & n_657=(m_856-m)+n & h_658=h-1 & 1<=m_856 & m_856<=(m-2) & 
  m<=(m_856+n) & 1<=k_857 & 2<=h | k=h & n_657=(m_856+n)-m & 1<=k_857 & 
  k_857<=(h-2) & 1<=m_856 & m_856<=(m-2) & 0<=h_658 & h_658<=(h-2) & 
  m<=(m_856+n) | n_657=(m_856+n)-m & h_658=h-1 & 1<=k_857 & k_857<=(k-2) & 
  1<=m_856 & m_856<=(m-2) & k<=h & m<=(m_856+n) | k=k_857+1 & n_657=(m_856+
  n)-m & 1<=m_856 & m_856<=(m-2) & (h_658+2)<=h & h<=(k_857+1) & m<=(m_856+
  n) & 0<=h_658) & A(n_657,h_658,m_856,k_857)) --> A(n,h,m,k),
 ((k=k_895+1 & h_674=h-1 & n_673=(m_894+n)-m & 1<=m_894 & m_894<=(m-2) & 
  m<=(m_894+n) & 2<=k_895 & 3<=h | k=k_895+1 & n_673=(m_894-m)+n & (h_674+
  1)<=h & 2<=h & h<=k_895 & 1<=m_894 & m_894<=(m-2) & 0<=h_674 & m<=(m_894+
  n) | k=h & n_673=(m_894-m)+n & 1<=m_894 & m_894<=(m-2) & 1<=k_895 & 
  k_895<h & 0<=h_674 & h_674<h & m<=(m_894+n) | h_674=h-1 & n_673=(m_894-m)+
  n & 1<=k_895 & k_895<k & k<h & 1<=m_894 & m_894<=(m-2) & m<=(m_894+n)) & 
  A(n_673,h_674,m_894,k_895)) --> A(n,h,m,k)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node3 SUCCESS

Termination checking result:

Stop Omega... 223 invocations 
0 false contexts at: ()

Total verification time: 0.39 second(s)
	Time spent in main process: 0.12 second(s)
	Time spent in child processes: 0.27 second(s)
