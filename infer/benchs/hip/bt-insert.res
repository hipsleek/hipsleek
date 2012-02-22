
Processing file "bt-insert.ss"
Parsing bt-insert.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure insert$node3... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0 | h!=0, n!=0 | h!=0, n!=0 | h!=0, n!=0 | h!=0]
!!! REL :  A(n,h,m,k)
!!! POST:  k>=2 & k>=h & (h+1)>=k & (k+m)>=(3+h) & m=n+1
!!! PRE :  1<=n & 1<=h
!!! OLD SPECS: ((None,[]),EInfer [A,n,h]
              EBase exists (Expl)(Impl)[n; h](ex)x::bt<n,h>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m,k: x::bt<m,k>@M[Orig][LHSCase]&
                                A(n,h,m,k)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; h](ex)x::bt<n,h>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&1<=n & 1<=h & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::bt<m,k>@M[Orig][LHSCase]&k>=2 & k>=h & (h+
                              1)>=k & (k+m)>=(3+h) & m=n+1 & 0<=n & 0<=h&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(hq_693:k=2 & m=2 & n=1 & h=1 | 1+n=m & 3<=m & -1+k=hq_693 & -1+
  h=hq_693 & 2<=hq_693 | k=2 & h=2 & 1+n=m & 3<=m)) --> A(n,h,m,k),
 (-1+m=n & k=h & 2<=h & 2<=n) --> A(n,h,m,k),
 (exists(hq_594:exists(hp_591:exists(hq_864:(1+k_857=k & hq_594=hq_864 & 1+
  h_658=h & 1+hp_591=h & 1<=hq_864 & (1+hq_864)<=k & (1+hq_864)<=h | -1+
  k=hq_864 & hq_594=hq_864 & -1+h=hq_864 & hp_591=h_658 & 0<=h_658 & (1+
  h_658)<=hq_864 & 1<=k_857 & (1+k_857)<=hq_864 | -1+k=hq_864 & 
  hq_594=hq_864 & 1+h_658=h & 1+hp_591=h & 1<=k_857 & (1+k_857)<=hq_864 & (1+
  hq_864)<=h | 1+k_857=k & hq_594=hq_864 & -1+h=hq_864 & hp_591=h_658 & 
  0<=h_658 & (1+h_658)<=hq_864 & (1+hq_864)<=k) & 
  A(n_657,h_658,m_856,k_857) & 1<=m_856 & (m_856+n+n)<=(-2+m+n+n) & m+n+
  n_657=m_856+n+n & (m+n)<=(m_856+n+n))))) --> A(n,h,m,k),
 (exists(hq_594:exists(hp_899:exists(hp_591:(hq_594=h_674 & -1+h=h_674 & 1+
  k_895=k & hp_591=hp_899 & 1<=hp_899 & (2+hp_899)<=k & (1+hp_899)<=h_674 | 
  hq_594=h_674 & 1+hp_899=h & 1+k_895=k & 1+hp_591=h & 0<=h_674 & (1+
  h_674)<=h & (1+h)<=k & 2<=h | hq_594=h_674 & h=k & 1+hp_899=k & 1+
  hp_591=k & 0<=h_674 & (1+h_674)<=k & 1<=k_895 & (1+k_895)<=k | 
  hq_594=h_674 & -1+h=h_674 & 1+hp_899=k & 1+hp_591=k & 1<=k_895 & (1+
  k_895)<=k & k<=h_674) & A(n_673,h_674,m_894,k_895) & 1<=m_894 & (m_894+n+
  n)<=(-2+m+n+n) & m+n+n_673=m_894+n+n & (m+n)<=(m_894+n+
  n))))) --> A(n,h,m,k)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node3 SUCCESS

Termination checking result:

Stop Omega... 329 invocations 
0 false contexts at: ()

Total verification time: 1.6 second(s)
	Time spent in main process: 0.83 second(s)
	Time spent in child processes: 0.77 second(s)
