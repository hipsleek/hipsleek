
Processing file "dll_size.ss"
Parsing dll_size.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node~node... 
!!! REL :  APP2(t,n,m)
!!! POST:  n>=0 & t>=(1+n) & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{524}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([null!=x][0<=m & 0!=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                EXISTS(q_188,
                                t: x::dll<q_188,t>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=t & APP2(t,n,m)][q=q_188]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{524}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([x!=null][1<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              EXISTS(q_1673,
                              t_1674: x::dll<q_1673,t_1674>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=t_1674 & 0<=m & t_1674=m+n & 0<=n & (1+
                                 n)<=t_1674]
                               [q=q_1673]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (t=1 & n=0 & m=1) --> APP2(t,n,m),
 (m=1 & t=n+1 & 1<=n) --> APP2(t,n,m),
 (t=1 & m=1 & n=0) --> APP2(t,n,m),
 (m=m_1573+1 & n=n_1575 & t=t_1648+1 & 1<=m_1573 & 0<=n_1575 & 1<=t_1648 & 
  APP2(t_1648,n_1575,m_1573)) --> APP2(t,n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! REL :  ASSIGN(n,n1,m)
!!! POST:  m>=0 & n>=0 & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ASSIGN]
              EBase exists (Expl)(Impl)[Anon_28; 
                    m](ex)x::dll<Anon_28,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::ref [x]
                                EXISTS(Anon_29,
                                n1: x'::dll<Anon_29,n1>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=n1 & ASSIGN(n,n1,m)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_28; 
                  m](ex)x::dll<Anon_28,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 17::ref [x]
                              EXISTS(Anon_1830,
                              n1_1831: x'::dll<Anon_1830,n1_1831>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([n=n1_1831 & 0<=n][0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=n & 0<=n & 0<=m) --> ASSIGN(n,n1,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=1, a!=1 | n!=0, a!=1 | n!=1, a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  DEL(n,a,m)
!!! POST:  a>=1 & n>=(1+a) & n=m+1
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [DEL,n,a]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(p_175,
                                m: x::dll<p_175,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & DEL(n,a,m)][p=p_175]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & (1+a)<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 54::
                              EXISTS(p_2093,
                              m_2094: x::dll<p_2093,m_2094>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=m_2094 & 0<=n & -1+n=m_2094 & (1+a)<=n & 
                                 1<=a]
                               [p=p_2093]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=1 & n=m+1 & 2<=m) --> DEL(n,a,m),
 (m=1 & n=2 & a=1) --> DEL(n,a,m),
 ((a=v_int_308_2068+1 & m_2067=m-1 & n=n_1996+1 & 1<=m & 0<=n_1996 & 
  1<=v_int_308_2068 | a=v_int_308_2068+1 & m_2067=m-1 & n=n_1996+1 & 
  v_int_308_2068<=(0-1) & 1<=m & 0<=n_1996) & 
  DEL(n_1996,v_int_308_2068,m_2067)) --> DEL(n,a,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[Anon_53; 
                    n](ex)x::dll<Anon_53,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 62::ref [x]
                                EXISTS(Anon_54,
                                m: res::dll<Anon_54,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & DEL2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_53; 
                  n](ex)x::dll<Anon_53,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 62::ref [x]
                              EXISTS(Anon_2358,
                              m_2359: res::dll<Anon_2358,m_2359>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([m_2359<=n & 0<=n & 0<=m_2359 & (-1+n)<=m_2359]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> DEL2(m,n),
 (m=n-1 & 2<=n) --> DEL2(m,n),
 (m=0 & n=1) --> DEL2(m,n),
 (m=m_2212+1 & n_2191=n-1 & 1<=m_2212 & 1<=n & 
  DEL2(m_2212,n_2191)) --> DEL2(m,n),
 (m=1 & m_2212=0 & n_2191=n-1 & 1<=n & DEL2(m_2212,n_2191)) --> DEL2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
!!! REL :  EMPT1(res)
!!! POST:  res
!!! PRE :  true
!!! REL :  EMPT2(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [EMPT1,EMPT2]
              EBase exists (Expl)(Impl)[Anon_17; 
                    n](ex)x::dll<Anon_17,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 4::
                                                         true&(
                                                         ([EMPT1(res)]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             n!=0 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 5::
                                                          true&(
                                                          ([EMPT2(res)]))&
                                                          {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_17; 
                  n](ex)x::dll<Anon_17,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 4::
                                                       true&(
                                                       ([res][0=n & 0<=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           n!=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                    {FLOW,(1,23)=__flow}
                                                      EAssume 5::
                                                        true&(
                                                        ([!(res)]
                                                         [n!=0 & 0<=n]))&
                                                        {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (1<=res) --> EMPT1(res),
 (res<=0) --> EMPT2(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(m,v)
!!! POST:  m>=(1+v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[Anon_62; 
                    n](ex)x::dll<Anon_62,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 126::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_63,Anon_64,
                                   m: res::node<m,Anon_63,Anon_64>@M[Orig][]&
                                   (([FGE(m,v)][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_62; 
                  n](ex)x::dll<Anon_62,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 126::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_2488,Anon_2489,
                                 m_2490: res::node<m_2490,Anon_2488,Anon_2489>@M[Orig][]&
                                 (([(1+v)<=m_2490][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (v<m) --> FGE(m,v),
 (m_2486=m & FGE(m_2486,v)) --> FGE(m,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! REL :  FRONT(res,v)
!!! POST:  v=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FRONT]
              EBase exists (Expl)(Impl)[v; p; q; Anon_20; 
                    Anon_21](ex)x::node<v,p,q>@M[Orig][] * 
                    q::dll<Anon_20,Anon_21>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([x!=null][0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(([FRONT(res,v)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; p; q; Anon_20; 
                  Anon_21](ex)x::node<v,p,q>@M[Orig][] * 
                  q::dll<Anon_20,Anon_21>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([x!=null][0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              true&(([res=v][0<=Anon_21]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=v) --> FRONT(res,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(m,n)
!!! POST:  m>=0 & m+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[Anon_37; 
                    n](ex)x::dll<Anon_37,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                EXISTS(flted_222_185,flted_222_186,Anon_38,
                                Anon_39,
                                m: x::node<Anon_38,flted_222_186,flted_222_185>@M[Orig][] * 
                                res::dll<Anon_39,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (
                                ([null=flted_222_186][null=flted_222_185]
                                 [0<=m & GN(m,n)][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_37; 
                  n](ex)x::dll<Anon_37,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              EXISTS(flted_222_2538,flted_222_2539,Anon_2540,
                              Anon_2541,
                              m_2542: x::node<Anon_2540,flted_222_2539,flted_222_2538>@M[Orig][] * 
                              res::dll<Anon_2541,m_2542>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([1+m_2542=n & 0<=n & 0<=m_2542][x!=null]
                               [null=flted_222_2538][null=flted_222_2539]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 1<=n) --> GN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1]
!!! REL :  GNN(m,n)
!!! POST:  m>=0 & m+2=n
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[Anon_51; 
                    n](ex)x::dll<Anon_51,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(Anon_52,
                                m: res::dll<Anon_52,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & GNN(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_51; 
                  n](ex)x::dll<Anon_51,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(Anon_2607,
                              m_2608: res::dll<Anon_2607,m_2608>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([2+m_2608=n & 0<=n & 0<=m_2608]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-2 & 2<=n) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INSERT(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(p_178,
                                m: x::dll<p_178,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & INSERT(m,n)][p=p_178]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(p_2725,
                              m_2726: x::dll<p_2725,m_2726>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=m_2726 & 0<=n & -1+m_2726=n & 2<=m_2726]
                               [p=p_2725]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=2 & n=1) --> INSERT(m,n),
 (n_2656=n-1 & m=m_2700+1 & 2<=n & 1<=m_2700 & 
  INSERT(m_2700,n_2656)) --> INSERT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 94::
                                EXISTS(p_154,n_155,Anon_59,
                                m: x::dll<p_154,n_155>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                                res::dll<Anon_59,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (
                                ([p=p_154]
                                 [n=n_155 & 0<=n_155 & 0<=m & CPY(m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 94::
                              EXISTS(p_2954,n_2955,Anon_2956,
                              m_2957: x::dll<p_2954,n_2955>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                              res::dll<Anon_2956,m_2957>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([n=n_2955 & n=m_2957 & 0<=n][p=p_2954]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_2760=n-1 & m=m_2780+1 & 1<=n & 1<=m_2780 & 
  CPY(m_2780,n_2760)) --> CPY(m,n),
 (m_2780=0 & m=1 & n_2760=n-1 & 1<=n & CPY(m_2780,n_2760)) --> CPY(m,n),
 (m=0 & n=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  m>=0 & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[Anon_60; 
                    n](ex)x::dll<Anon_60,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 116::ref [x]
                                EXISTS(Anon_61,
                                m: res::dll<Anon_61,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & FIL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_60; 
                  n](ex)x::dll<Anon_60,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 116::ref [x]
                              EXISTS(Anon_3169,
                              m_3170: res::dll<Anon_3169,m_3170>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([m_3170<=n & 0<=n & 0<=m_3170]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_3006=n-1 & m=m_3097 & 1<=n & 0<=m_3097 & FIL(m_3097,n_3006)) --> FIL(m,n),
 (m=m_3049+1 & n_3026=n-1 & 1<=m_3049 & 1<=n & 
  FIL(m_3049,n_3026)) --> FIL(m,n),
 (m=1 & m_3045=0 & n_3026=n-1 & 1<=n & FIL(m_3045,n_3026)) --> FIL(m,n),
 (m=0 & n=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! REL :  RMV(m,n)
!!! POST:  m>=1 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 99::
                                EXISTS(p_152,
                                m: x::dll<p_152,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & RMV(m,n)][p=p_152]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{524}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 99::
                              EXISTS(p_3471,
                              m_3472: x::dll<p_3471,m_3472>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=m_3472 & 0<=n & m_3472<=n & (-1+
                                 n)<=m_3472 & 1<=m_3472]
                               [p=p_3471]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 3<=n) --> RMV(m,n),
 (m=1 & n=2) --> RMV(m,n),
 (n=n_3334+1 & m=m_3424+1 & 1<=m_3424 & 1<=n_3334 & 
  RMV(m_3424,n_3334)) --> RMV(m,n),
 (m=1 & n=1) --> RMV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
!!! REL :  RMV2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 105::
                                EXISTS(p_150,
                                m: res::dll<p_150,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & RMV2(m,n)][p=p_150]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 105::
                              EXISTS(p_3734,
                              m_3735: res::dll<p_3734,m_3735>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([m_3735<=n & 0<=n & 0<=m_3735 & (-1+n)<=m_3735]
                               [p=p_3734]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 2<=n) --> RMV2(m,n),
 (m=0 & n=1) --> RMV2(m,n),
 (m=m_3594+1 & n_3577=n-1 & 1<=m_3594 & 1<=n & 
  RMV2(m_3594,n_3577)) --> RMV2(m,n),
 (m=1 & m_3592=0 & n_3577=n-1 & 1<=n & RMV2(m_3592,n_3577)) --> RMV2(m,n),
 (m=0 & n=0) --> RMV2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 91::
                                EXISTS(p_158,
                                m: x::dll<p_158,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & TRAV(m,n)][p=p_158]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 91::
                              EXISTS(p_3810,
                              m_3811: x::dll<p_3810,m_3811>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([n=m_3811 & 0<=n][p=p_3810]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (n_3770=n-1 & m=m_3779+1 & 1<=n & 0<=m_3779 & 
  TRAV(m_3779,n_3770)) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(n,m)
!!! POST:  n>=0 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_33; 
                    m](ex)x::dll<Anon_33,m>@M[Orig][LHSCase]@ rem br[{524}]&(
                    ([null!=x][0<=m & 0!=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::ref [x]
                                EXISTS(Anon_34,
                                n: x'::dll<Anon_34,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=n & PF(n,m)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_33; 
                  m](ex)x::dll<Anon_33,m>@M[Orig][LHSCase]@ rem br[{524}]&(
                  ([x!=null][1<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::ref [x]
                              EXISTS(Anon_3925,
                              n_3926: x'::dll<Anon_3925,n_3926>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([1+n_3926=m & 0<=m & 0<=n_3926]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & m=1) --> PF(n,m),
 (n=m-1 & 2<=m) --> PF(n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_30; 
                    n](ex)x::dll<Anon_30,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::ref [x]
                                EXISTS(v_191,Anon_31,q,Anon_32,
                                m: x'::node<v_191,Anon_31,q>@M[Orig][] * 
                                q::dll<Anon_32,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m & PUF(m,n)][v=v_191][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; 
                  n](ex)x::dll<Anon_30,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 19::ref [x]
                              EXISTS(v_3996,Anon_3997,q_3998,Anon_3999,
                              m_4000: x'::node<v_3996,Anon_3997,q_3998>@M[Orig][] * 
                              q_3998::dll<Anon_3999,m_4000>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([n=m_4000 & 0<=n][x'!=null][v=v_3996]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> PUF(m,n),
 (m=n & 1<=n) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! REL :  RF(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RF]
              EBase exists (Expl)(Impl)[Anon_35; 
                    m](ex)x::dll<Anon_35,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(Anon_36,
                                n: x::dll<Anon_36,n>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=n & RF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_35; 
                  m](ex)x::dll<Anon_35,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(Anon_4005,
                              n_4006: x::dll<Anon_4005,n_4006>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (([m=n_4006 & 0<=m]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=m & 0<=m) --> RF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
!!! REL :  REV(k,m,n)
!!! POST:  n>=0 & k>=n & k=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[p; n; q; 
                    m](ex)xs::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                    ys::dll<q,m>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::ref [xs;ys]
                                EXISTS(Anon_56,
                                k: ys'::dll<Anon_56,k>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([null=xs'][0<=k & REV(k,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; q; 
                  m](ex)xs::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                  ys::dll<q,m>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::ref [xs;ys]
                              EXISTS(Anon_4214,
                              k_4215: ys'::dll<Anon_4214,k_4215>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=k_4215 & k_4215=m+n & 0<=m & 0<=n & 
                                 n<=k_4215]
                               [xs'=null]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_4092=n-1 & m=m_4094-1 & k=k_4179 & 1<=n & 2<=m_4094 & 0<=k_4179 & 
  REV(k_4179,m_4094,n_4092)) --> REV(k,m,n),
 (m_4094=1 & n_4092=n-1 & m=0 & k=k_4187 & 1<=n & 0<=k_4187 & 
  REV(k_4187,m_4094,n_4092)) --> REV(k,m,n),
 (n_4092=n-1 & m=m_4094-1 & k=k_4198 & 1<=n & 2<=m_4094 & 0<=k_4198 & 
  REV(k_4198,m_4094,n_4092)) --> REV(k,m,n),
 (m_4094=1 & n_4092=n-1 & m=0 & k=k_4206 & 1<=n & 0<=k_4206 & 
  REV(k_4206,m_4094,n_4092)) --> REV(k,m,n),
 (n=0 & k=m & 0<=m) --> REV(k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(k,j)
!!! POST:  k>=1 & k=j+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[Anon_40; i; Anon_41; 
                    j](ex)x::dll<Anon_40,i>@M[Orig][LHSCase]@ rem br[{524}] * 
                    y::dll<Anon_41,j>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([null!=x][0<=i & 0!=i][0<=j]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(Anon_42,
                                k: x::dll<Anon_42,k>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=k & SN(k,j)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_40; i; Anon_41; 
                  j](ex)x::dll<Anon_40,i>@M[Orig][LHSCase]@ rem br[{524}] * 
                  y::dll<Anon_41,j>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([x!=null][1<=i][0<=j]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              EXISTS(Anon_4374,
                              k_4375: x::dll<Anon_4374,k_4375>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=k_4375 & 0<=j & -1+k_4375=j & 1<=k_4375]
                               [0<=i]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (k=1 & j=0) --> SN(k,j),
 (k=j+1 & 1<=j) --> SN(k,j)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
!!! REL :  SIZEH(res,m,n)
!!! POST:  m>=0 & res=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SIZEH]
              EBase exists (Expl)(Impl)[Anon_18; 
                    m](ex)x::dll<Anon_18,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&(([SIZEH(res,m,n)]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_18; 
                  m](ex)x::dll<Anon_18,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&(([0<=m & res=m+n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (v_int_55_1386'=res & m_4505=m-1 & 1<=m & SIZEH(v_int_55_1386',m_4505,n+
  1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,m)
!!! POST:  res>=0 & res=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[Anon_19; 
                    m](ex)x::dll<Anon_19,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(([SIZE(res,m)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; 
                  m](ex)x::dll<Anon_19,m>@M[Orig][LHSCase]@ rem br[{525,524}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&(([m=res & 0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=res & 0<=res) --> SIZE(res,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
!!! REL :  SPLICE(t,m,n)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLICE]
              EBase exists (Expl)(Impl)[Anon_65; n; Anon_66; 
                    m](ex)x::dll<Anon_65,n>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                    y::dll<Anon_66,m>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 129::ref [x]
                                EXISTS(Anon_67,
                                t: x'::dll<Anon_67,t>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=t & SPLICE(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_65; n; Anon_66; 
                  m](ex)x::dll<Anon_65,n>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                  y::dll<Anon_66,m>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 129::ref [x]
                              EXISTS(Anon_4776,
                              t_4777: x'::dll<Anon_4776,t_4777>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([0<=t_4777 & t_4777=m+n & 0<=m & 0<=n & 
                                 n<=t_4777]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (t_4636=0 & t=2 & n_4613=n-1 & m_4615=m-1 & 1<=n & 1<=m & 
  SPLICE(t_4636,m_4615,n_4613)) --> SPLICE(t,m,n),
 (n=0 & t=m & 0<=m) --> SPLICE(t,m,n),
 (m_4615=m-1 & n_4613=n-1 & t=t_4636+2 & 1<=m & 1<=n & 1<=t_4636 & 
  SPLICE(t_4636,m_4615,n_4613)) --> SPLICE(t,m,n),
 (t_4636=0 & t=2 & n_4613=n-1 & m_4615=m-1 & 1<=m & 1<=n & 
  SPLICE(t_4636,m_4615,n_4613)) --> SPLICE(t,m,n),
 (m=0 & t=n & 1<=n) --> SPLICE(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  SPLIT(n,a,n1,n2)
!!! POST:  a>=1 & n2>=0 & a=n1 & a+n2=n
!!! PRE :  1<=a & a<=n
!!! OLD SPECS: ((None,[]),EInfer [SPLIT,n,a]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::ref [x]
                                EXISTS(p_160,Anon_57,n1,
                                n2: x'::dll<p_160,n1>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                                res::dll<Anon_57,n2>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (
                                ([0<=n1 & 0<=n2 & SPLIT(n,a,n1,n2)][p=p_160]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & a<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 84::ref [x]
                              EXISTS(p_4932,Anon_4933,n1_4934,
                              n2_4935: x'::dll<p_4932,n1_4934>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                              res::dll<Anon_4933,n2_4935>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([a=n1_4934 & a+n2_4935=n & 0<=n & 
                                 0<=n2_4935 & 0<=n1_4934 & 1<=a]
                               [p=p_4932]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=1 & a=1 & n2=n-1 & 1<=n) --> SPLIT(n,a,n1,n2),
 ((a=a_4904+1 & n2_4902=n2 & n1_4901=n1-1 & n=n_4850+1 & 0<=n2 & 1<=n1 & 
  0<=n_4850 & 1<=a_4904 | a=a_4904+1 & n2_4902=n2 & n1_4901=n1-1 & n=n_4850+
  1 & a_4904<=(0-1) & 0<=n2 & 1<=n1 & 0<=n_4850) & 
  SPLIT(n_4850,a_4904,n1_4901,n2_4902)) --> SPLIT(n,a,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_24; m; Anon_25; 
                    n](ex)x::dll<Anon_24,m>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                    y::dll<Anon_25,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::ref [x;y]
                                EXISTS(Anon_26,m1,Anon_27,
                                n1: x'::dll<Anon_26,m1>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                                y'::dll<Anon_27,n1>@M[Orig][LHSCase]@ rem br[{525,524}]&
                                (([0<=m1][0<=n1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_24; m; Anon_25; 
                  n](ex)x::dll<Anon_24,m>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                  y::dll<Anon_25,n>@M[Orig][LHSCase]@ rem br[{525,524}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 14::ref [x;y]
                              EXISTS(Anon_4945,m1_4946,Anon_4947,
                              n1_4948: x'::dll<Anon_4945,m1_4946>@M[Orig][LHSCase]@ rem br[{525,524}] * 
                              y'::dll<Anon_4947,n1_4948>@M[Orig][LHSCase]@ rem br[{525,524}]&
                              (
                              ([m=n1_4948 & 0<=m][n=m1_4946 & 0<=n][y=x']
                               [x=y'][Anon_4945=Anon_25][Anon_4947=Anon_24]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 2240 invocations 
7 false contexts at: ( (546,6)  (252,13)  (252,4)  (41,17)  (41,24)  (42,7)  (42,14) )

Total verification time: 1.64 second(s)
	Time spent in main process: 0.67 second(s)
	Time spent in child processes: 0.97 second(s)
