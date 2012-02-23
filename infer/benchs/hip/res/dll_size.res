
Processing file "dll_size.ss"
Parsing dll_size.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  APP(t,m,n)
!!! POST:  m>=0 & n>=0 & m+n=t
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{221,220}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::
                                EXISTS(Anon_12,
                                t: res::dll<Anon_12,t>@M[Orig][LHSCase]@ rem br[{221,220}]&
                                (([0<=t & APP(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{221,220}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 18::
                              res::dll<Anon_12,t>@M[Orig][LHSCase]@ rem br[{221,220}]&
                              (([0<=t & m+n=t & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> APP(t,m,n),
 (0<=m_790 & n_792=n & 1+t_817=t & -1+m=m_790 & 2<=t & 
  APP(t_817,m_790,n_792) & 0<=n) --> APP(t,m,n),
 (0<=m_790 & t_813=0 & t=1 & n_792=n & -1+m=m_790 & 0<=n & 
  APP(t_813,m_790,n_792)) --> APP(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure append1$node2~node2... 
!!! REL :  APP1(t,m,n)
!!! POST:  m>=0 & t>=m & t=n+m
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [APP1]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{221,220}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(Anon_13,
                                t: res::dll<Anon_13,t>@M[Orig][LHSCase]@ rem br[{221,220}]&
                                (([0<=t & APP1(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{221,220}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              res::dll<Anon_13,t>@M[Orig][LHSCase]@ rem br[{221,220}]&
                              (([0<=t & t=m+n & 0<=n & 0<=m & m<=t]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=m_958 & t_981=0 & t=1 & n_960=n & -1+m=m_958 & 0<=n & 
  APP1(t_981,m_958,n_960)) --> APP1(t,m,n),
 (m=0 & n=t & 0<=t) --> APP1(t,m,n),
 (0<=m_958 & -1+m=m_958 & 1+t_985=t & n_960=n & 2<=t & 
  APP1(t_985,m_958,n_960) & 0<=n) --> APP1(t,m,n),
 (0<=m_958 & t_981=0 & t=1 & n_960=n & -1+m=m_958 & 0<=n & 
  APP1(t_981,m_958,n_960)) --> APP1(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append1$node2~node2 SUCCESS

Checking procedure append2$node2~node2... 
!!! REL :  APP2(t,n,m)
!!! POST:  n>=0 & t>=(1+n) & t=m+n
!!! PRE :  0<=n & 1<=m
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{220}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                    ([null!=x][0<=m & 0!=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                EXISTS(q_45,
                                t: x::dll<q_45,t>@M[Orig][LHSCase]@ rem br[{221,220}]&
                                (([0<=t & APP2(t,n,m)][q=q_45]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{220}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                  ([x!=null][1<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n][1<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              x::dll<q_45,t>@M[Orig][LHSCase]@ rem br[{221,220}]&
                              (
                              ([0<=t & 0<=m & t=m+n & 0<=n & (1+n)<=t]
                               [q_45=q]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (t=1 & n=0 & m=1) --> APP2(t,n,m),
 (m=1 & 1+n=t & 2<=t) --> APP2(t,n,m),
 (t=1 & m=1 & n=0) --> APP2(t,n,m),
 (n_1181=n & 1+t_1254=t & 0<=n & 2<=t & APP2(t_1254,n_1181,m_1179) & 
  1<=m_1179 & -1+m=m_1179) --> APP2(t,n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node2~node2 SUCCESS

Checking procedure delete$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=1, a!=1 | n!=0, a!=1 | n!=1, a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  DEL(n,a,m)
!!! POST:  a>=1 & m>=a & m+1=n
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [DEL,n,a]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(p_51,
                                m: x::dll<p_51,m>@M[Orig][LHSCase]@ rem br[{221,220}]&
                                (([0<=m & DEL(n,a,m)][p=p_51]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & (1+a)<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 4::
                              x::dll<p_51,m>@M[Orig][LHSCase]@ rem br[{221,220}]&
                              (
                              ([0<=m & 0<=n & 1+m=n & a<=m & 1<=a][p_51=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (a=1 & 2<=m & -1+n=m) --> DEL(n,a,m),
 (m=1 & n=2 & a=1) --> DEL(n,a,m),
 ((1<=v_int_51_1515 | v_int_51_1515<=-1) & 
  DEL(n_1443,v_int_51_1515,m_1514) & 1<=m & -1+n=n_1443 & 1+m_1514=m & -1+
  a=v_int_51_1515 & 0<=n_1443) --> DEL(n,a,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Checking procedure delete1$node2~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=1, a!=1 | n!=0, a!=1 | n!=1, a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  DEL1(n,m,a)
!!! POST:  a>=1 & n>=(1+a) & n=m+1
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [DEL1,n,a]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                EXISTS(p_49,
                                m: x::dll<p_49,m>@M[Orig][LHSCase]@ rem br[{221,220}]&
                                (([0<=m & DEL1(n,m,a)][p=p_49]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{221,220}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & (1+a)<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 12::
                              x::dll<p_49,m>@M[Orig][LHSCase]@ rem br[{221,220}]&
                              (
                              ([0<=m & 0<=n & -1+n=m & (1+a)<=n & 1<=a]
                               [p_49=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (a=1 & -1+n=m & 2<=m) --> DEL1(n,m,a),
 (m=1 & n=2 & a=1) --> DEL1(n,m,a),
 ((1<=v_int_73_1752 | v_int_73_1752<=-1) & 
  DEL1(n_1682,m_1751,v_int_73_1752) & 1<=m & -1+n=n_1682 & 1+m_1751=m & -1+
  a=v_int_73_1752 & 0<=n_1682) --> DEL1(n,m,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete1$node2~int SUCCESS

Checking procedure insert$node2~int... 
!!! REL :  INSERT(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{220}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(p_54,
                                m: x::dll<p_54,m>@M[Orig][LHSCase]@ rem br[{221,220}]&
                                (([0<=m & INSERT(m,n)][p=p_54]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{220}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              x::dll<p_54,m>@M[Orig][LHSCase]@ rem br[{221,220}]&
                              (([0<=m & 0<=n & -1+m=n & 2<=m][p_54=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=2 & n=1) --> INSERT(m,n),
 (1<=n_1824 & -1+n=n_1824 & 1+m_1868=m & INSERT(m_1868,n_1824) & 
  2<=m) --> INSERT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Termination checking result:

Stop Omega... 732 invocations 
0 false contexts at: ()

Total verification time: 1.65 second(s)
	Time spent in main process: 1.22 second(s)
	Time spent in child processes: 0.43 second(s)
