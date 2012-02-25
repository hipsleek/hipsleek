
Processing file "dll_size.ss"
Parsing dll_size.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! REL :  APP(t,m,n)
!!! POST:  m>=0 & n>=0 & m+n=t
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                EXISTS(Anon_35,
                                t: res::dll<Anon_35,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=t & APP(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              res::dll<Anon_35,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=t & m+n=t & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=t & 0<=t) --> APP(t,m,n),
 (0<=m_1597 & n_1599=n & 1+t_1624=t & -1+m=m_1597 & 2<=t & 
  APP(t_1624,m_1597,n_1599) & 0<=n) --> APP(t,m,n),
 (0<=m_1597 & t_1620=0 & t=1 & n_1599=n & -1+m=m_1597 & 0<=n & 
  APP(t_1620,m_1597,n_1599)) --> APP(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure append1$node~node... 
!!! REL :  APP1(t,m,n)
!!! POST:  m>=0 & t>=m & t=n+m
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [APP1]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(Anon_36,
                                t: res::dll<Anon_36,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=t & APP1(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              res::dll<Anon_36,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=t & t=m+n & 0<=n & 0<=m & m<=t]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=m_1765 & t_1788=0 & t=1 & n_1767=n & -1+m=m_1765 & 0<=n & 
  APP1(t_1788,m_1765,n_1767)) --> APP1(t,m,n),
 (m=0 & n=t & 0<=t) --> APP1(t,m,n),
 (0<=m_1765 & -1+m=m_1765 & 1+t_1792=t & n_1767=n & 2<=t & 
  APP1(t_1792,m_1765,n_1767) & 0<=n) --> APP1(t,m,n),
 (0<=m_1765 & t_1788=0 & t=1 & n_1767=n & -1+m=m_1765 & 0<=n & 
  APP1(t_1788,m_1765,n_1767)) --> APP1(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append1$node~node SUCCESS

Checking procedure append2$node~node... 
!!! REL :  APP2(t,n,m)
!!! POST:  n>=0 & t>=(1+n) & t=m+n
!!! PRE :  0<=n & 1<=m
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{565}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([null!=x][0<=m & 0!=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::
                                EXISTS(q_196,
                                t: x::dll<q_196,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=t & APP2(t,n,m)][q=q_196]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{565}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([x!=null][1<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n][1<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 43::
                              x::dll<q_196,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (
                              ([0<=t & 0<=m & t=m+n & 0<=n & (1+n)<=t]
                               [q_196=q]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (t=1 & n=0 & m=1) --> APP2(t,n,m),
 (m=1 & 1+n=t & 2<=t) --> APP2(t,n,m),
 (t=1 & m=1 & n=0) --> APP2(t,n,m),
 (n_1988=n & 1+t_2061=t & 0<=n & 2<=t & APP2(t_2061,n_1988,m_1986) & 
  1<=m_1986 & -1+m=m_1986) --> APP2(t,n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! REL :  ASSIGN(n,n1,m)
!!! POST:  m>=0 & n1>=0 & n1=n
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [ASSIGN]
              EBase exists (Expl)(Impl)[Anon_28; 
                    m](ex)x::dll<Anon_28,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::ref [x]
                                EXISTS(Anon_29,
                                n1: x'::dll<Anon_29,n1>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=n1 & ASSIGN(n,n1,m)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_28; 
                  m](ex)x::dll<Anon_28,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 17::ref [x]
                              x'::dll<Anon_29,n1>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([n=n1 & 0<=n1][0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=n1 & 0<=n1 & 0<=m) --> ASSIGN(n,n1,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=1, a!=1 | n!=0, a!=1 | n!=1, a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  DEL(n,a,m)
!!! POST:  a>=1 & m>=a & m+1=n
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [DEL,n,a]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 67::
                                EXISTS(p_183,
                                m: x::dll<p_183,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & DEL(n,a,m)][p=p_183]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & (1+a)<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 67::
                              x::dll<p_183,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (
                              ([0<=m & 0<=n & 1+m=n & a<=m & 1<=a][p_183=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (a=1 & 2<=m & -1+n=m) --> DEL(n,a,m),
 (m=1 & n=2 & a=1) --> DEL(n,a,m),
 ((1<=v_int_308_2477 | v_int_308_2477<=-1) & 
  DEL(n_2405,v_int_308_2477,m_2476) & 1<=m & -1+n=n_2405 & 1+m_2476=m & -1+
  a=v_int_308_2477 & 0<=n_2405) --> DEL(n,a,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[Anon_55; 
                    n](ex)x::dll<Anon_55,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 75::ref [x]
                                EXISTS(Anon_56,
                                m: res::dll<Anon_56,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & DEL2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_55; 
                  n](ex)x::dll<Anon_55,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 75::ref [x]
                              res::dll<Anon_56,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([m<=n & 0<=n & 0<=m & (-1+n)<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (DEL2(m_2619,n_2598) & -1+n=n_2598 & m=1 & m_2619=0 & 
  0<=n_2598) --> DEL2(m,n),
 (m=0 & n=0) --> DEL2(m,n),
 (-1+n=m & 1<=m) --> DEL2(m,n),
 (m=0 & n=1) --> DEL2(m,n),
 (DEL2(m_2619,n_2598) & 2<=m & 1+m_2619=m & -1+n=n_2598 & 
  0<=n_2598) --> DEL2(m,n),
 (DEL2(m_2619,n_2598) & -1+n=n_2598 & m=1 & m_2619=0 & 
  0<=n_2598) --> DEL2(m,n)]
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
                    n](ex)x::dll<Anon_17,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
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
                  n](ex)x::dll<Anon_17,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
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
              EBase exists (Expl)(Impl)[Anon_64; 
                    n](ex)x::dll<Anon_64,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 139::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_65,Anon_66,
                                   m: res::node<m,Anon_65,Anon_66>@M[Orig][]&
                                   (([FGE(m,v)][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_64; 
                  n](ex)x::dll<Anon_64,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 139::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_65,Anon_66>@M[Orig][]&(
                                 ([(1+v)<=m][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ ((1+v)<=m) --> FGE(m,v),
 (exists(Anon_2846:m=m_2891 & Anon_2846<=v & FGE(m_2891,v))) --> FGE(m,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! REL :  FRONT(res,v)
!!! POST:  res=v
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FRONT]
              EBase exists (Expl)(Impl)[v; p; q; Anon_20; 
                    Anon_21](ex)x::node<v,p,q>@M[Orig][] * 
                    q::dll<Anon_20,Anon_21>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([x!=null][0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(([FRONT(res,v)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; p; q; Anon_20; 
                  Anon_21](ex)x::node<v,p,q>@M[Orig][] * 
                  q::dll<Anon_20,Anon_21>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([x!=null][0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              true&(([v=res][0<=Anon_21]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (v=res) --> FRONT(res,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(m,n)
!!! POST:  n>=1 & n=m+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[Anon_39; 
                    n](ex)x::dll<Anon_39,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(flted_222_193,flted_222_194,Anon_40,
                                Anon_41,
                                m: x::node<Anon_40,flted_222_194,flted_222_193>@M[Orig][] * 
                                res::dll<Anon_41,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (
                                ([null=flted_222_194][null=flted_222_193]
                                 [0<=m & GN(m,n)][x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39; 
                  n](ex)x::dll<Anon_39,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              x::node<Anon_40,flted_222_194,flted_222_193>@M[Orig][] * 
                              res::dll<Anon_41,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (
                              ([0<=m & 0<=n & -1+n=m & 1<=n][x!=null]
                               [flted_222_193=null][flted_222_194=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 0<=m) --> GN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1]
!!! REL :  GNN(m,n)
!!! POST:  n>=2 & n=m+2
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[Anon_53; 
                    n](ex)x::dll<Anon_53,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 63::
                                EXISTS(Anon_54,
                                m: res::dll<Anon_54,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & GNN(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_53; 
                  n](ex)x::dll<Anon_53,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 63::
                              res::dll<Anon_54,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=m & 0<=n & -2+n=m & 2<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-2+n=m & 0<=m) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INSERT(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 64::
                                EXISTS(p_186,
                                m: x::dll<p_186,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & INSERT(m,n)][p=p_186]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 64::
                              x::dll<p_186,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=m & 0<=n & -1+m=n & 2<=m][p_186=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=2 & n=1) --> INSERT(m,n),
 (1<=n_3051 & -1+n=n_3051 & 1+m_3095=m & INSERT(m_3095,n_3051) & 
  2<=m) --> INSERT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 107::
                                EXISTS(p_162,n_163,Anon_61,
                                m: x::dll<p_162,n_163>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                                res::dll<Anon_61,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (
                                ([p=p_162]
                                 [n=n_163 & 0<=n_163 & 0<=m & CPY(m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 107::
                              x::dll<p_162,n_163>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                              res::dll<Anon_61,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([m=n & m=n_163 & 0<=n][p_162=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=n_3153 & m_3173=0 & m=1 & -1+n=n_3153 & CPY(m_3173,n_3153)) --> CPY(m,n),
 (0<=n_3153 & 1+m_3173=m & -1+n=n_3153 & 2<=m & 
  CPY(m_3173,n_3153)) --> CPY(m,n),
 (0<=n_3153 & m_3173=0 & m=1 & -1+n=n_3153 & CPY(m_3173,n_3153)) --> CPY(m,n),
 (m=0 & n=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  m>=0 & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[Anon_62; 
                    n](ex)x::dll<Anon_62,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 129::ref [x]
                                EXISTS(Anon_63,
                                m: res::dll<Anon_63,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & FIL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_62; 
                  n](ex)x::dll<Anon_62,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 129::ref [x]
                              res::dll<Anon_63,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([m<=n & 0<=n & 0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (FIL(m_3434,n_3415) & -1+n=n_3415 & m=1 & m_3434=0 & 0<=n_3415) --> FIL(m,n),
 (0<=n_3395 & m_3486=m & -1+n=n_3395 & FIL(m_3486,n_3395) & 
  0<=m) --> FIL(m,n),
 (FIL(m_3438,n_3415) & 2<=m & 1+m_3438=m & -1+n=n_3415 & 
  0<=n_3415) --> FIL(m,n),
 (FIL(m_3434,n_3415) & -1+n=n_3415 & m=1 & m_3434=0 & 0<=n_3415) --> FIL(m,n),
 (m=0 & n=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! REL :  RMV(m,n)
!!! POST:  m>=1 & (m+1)>=n & n>=m
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [RMV]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                    ([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 112::
                                EXISTS(p_160,
                                m: x::dll<p_160,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & RMV(m,n)][p=p_160]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{565}]&(
                  ([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 112::
                              x::dll<p_160,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (
                              ([0<=m & 0<=n & m<=n & (-1+n)<=m & 1<=m]
                               [p_160=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 2<=m) --> RMV(m,n),
 (m=1 & n=2) --> RMV(m,n),
 (2<=m & 2<=n & RMV(m_3811,n_3721) & 1+n_3721=n & 1+m_3811=m) --> RMV(m,n),
 (m=1 & n=1) --> RMV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
!!! REL :  RMV2(m,n)
!!! POST:  (m+1)>=n & m>=0 & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 118::
                                EXISTS(p_158,
                                m: res::dll<p_158,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & RMV2(m,n)][p=p_158]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 118::
                              res::dll<p_158,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([m<=n & 0<=n & (-1+n)<=m & 0<=m][p_158=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (RMV2(m_3977,n_3962) & -1+n=n_3962 & m=1 & m_3977=0 & 
  0<=n_3962) --> RMV2(m,n),
 (-1+n=m & 1<=m) --> RMV2(m,n),
 (m=0 & n=1) --> RMV2(m,n),
 (RMV2(m_3979,n_3962) & 2<=m & -1+n=n_3962 & 1+m_3979=m & 
  0<=n_3962) --> RMV2(m,n),
 (RMV2(m_3977,n_3962) & -1+n=n_3962 & m=1 & m_3977=0 & 
  0<=n_3962) --> RMV2(m,n),
 (m=0 & n=0) --> RMV2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 104::
                                EXISTS(p_166,
                                m: x::dll<p_166,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & TRAV(m,n)][p=p_166]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 104::
                              x::dll<p_166,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([n=m & 0<=n][p_166=p]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (0<=n_4153 & 1+m_4162=m & -1+n=n_4153 & 1<=m & 
  TRAV(m_4162,n_4153)) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(n,m)
!!! POST:  n>=0 & n+1=m
!!! PRE :  1<=m
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_33; 
                    m](ex)x::dll<Anon_33,m>@M[Orig][LHSCase]@ rem br[{565}]&(
                    ([null!=x][0<=m & 0!=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::ref [x]
                                EXISTS(Anon_34,
                                n: x'::dll<Anon_34,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=n & PF(n,m)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_33; 
                  m](ex)x::dll<Anon_33,m>@M[Orig][LHSCase]@ rem br[{565}]&(
                  ([x!=null][1<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 23::ref [x]
                              x'::dll<Anon_34,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([1+n=m & 0<=m & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & m=1) --> PF(n,m),
 (-1+m=n & 1<=n) --> PF(n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_30; 
                    n](ex)x::dll<Anon_30,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::ref [x]
                                EXISTS(v_201,Anon_31,q,Anon_32,
                                m: x'::node<v_201,Anon_31,q>@M[Orig][] * 
                                q::dll<Anon_32,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m & PUF(m,n)][v=v_201][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; 
                  n](ex)x::dll<Anon_30,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 19::ref [x]
                              x'::node<v_201,Anon_31,q>@M[Orig][] * 
                              q::dll<Anon_32,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([m=n & 0<=n][x'!=null][v_201=v]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=0) --> PUF(m,n),
 (n=m & 1<=m) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! REL :  RF(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  0<=m
!!! OLD SPECS: ((None,[]),EInfer [RF]
              EBase exists (Expl)(Impl)[Anon_37; 
                    m](ex)x::dll<Anon_37,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(Anon_38,
                                n: x::dll<Anon_38,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=n & RF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_37; 
                  m](ex)x::dll<Anon_37,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              x::dll<Anon_38,n>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([m=n & 0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=n & 0<=n) --> RF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
!!! REL :  REV(k,m,n)
!!! POST:  n>=0 & m>=0 & n+m=k
!!! PRE :  0<=n & 0<=m
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[p; n; q; 
                    m](ex)xs::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                    ys::dll<q,m>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 89::ref [xs;ys]
                                EXISTS(Anon_58,
                                k: ys'::dll<Anon_58,k>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([null=xs'][0<=k & REV(k,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; q; 
                  m](ex)xs::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                  ys::dll<q,m>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 89::ref [xs;ys]
                              ys'::dll<Anon_58,k>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=k & m+n=k & 0<=n & 0<=m][xs'=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=n_4464 & -1+n=n_4464 & k_4551=k & REV(k_4551,m_4466,n_4464) & 0<=k & 
  2<=m_4466 & 1+m=m_4466) --> REV(k,m,n),
 (0<=n_4464 & m_4466=1 & k_4559=k & -1+n=n_4464 & m=0 & 0<=k & 
  REV(k_4559,m_4466,n_4464)) --> REV(k,m,n),
 (0<=n_4464 & -1+n=n_4464 & k_4570=k & REV(k_4570,m_4466,n_4464) & 0<=k & 
  2<=m_4466 & 1+m=m_4466) --> REV(k,m,n),
 (0<=n_4464 & m_4466=1 & k_4578=k & -1+n=n_4464 & m=0 & 0<=k & 
  REV(k_4578,m_4466,n_4464)) --> REV(k,m,n),
 (m=k & n=0 & 0<=k) --> REV(k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(k,j)
!!! POST:  k>=1 & k=j+1
!!! PRE :  0<=j
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[Anon_42; i; Anon_43; 
                    j](ex)x::dll<Anon_42,i>@M[Orig][LHSCase]@ rem br[{565}] * 
                    y::dll<Anon_43,j>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([null!=x][0<=i & 0!=i][0<=j]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(Anon_44,
                                k: x::dll<Anon_44,k>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=k & SN(k,j)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_42; i; Anon_43; 
                  j](ex)x::dll<Anon_42,i>@M[Orig][LHSCase]@ rem br[{565}] * 
                  y::dll<Anon_43,j>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([x!=null][1<=i][0<=j]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=j]))&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              x::dll<Anon_44,k>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=k & 0<=j & -1+k=j & 1<=k][0<=i]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (k=1 & j=0) --> SN(k,j),
 (1+j=k & 2<=k) --> SN(k,j)]
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
!!! PRE :  0<=m
!!! OLD SPECS: ((None,[]),EInfer [SIZEH]
              EBase exists (Expl)(Impl)[Anon_18; 
                    m](ex)x::dll<Anon_18,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&(([SIZEH(res,m,n)]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_18; 
                  m](ex)x::dll<Anon_18,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&(([0<=m & res=m+n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (0<=m_4873 & res=v_int_55_1453' & -1+m=m_4873 & 
  SIZEH(v_int_55_1453',m_4873,n--1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,m)
!!! POST:  m>=0 & m=res
!!! PRE :  0<=m
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[Anon_19; 
                    m](ex)x::dll<Anon_19,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(([SIZE(res,m)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; 
                  m](ex)x::dll<Anon_19,m>@M[Orig][LHSCase]@ rem br[{566,565}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&(([res=m & 0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=m & 0<=m) --> SIZE(res,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
!!! REL :  SPLICE(t,m,n)
!!! POST:  n>=0 & m>=0 & n+m=t
!!! PRE :  0<=n & 0<=m
!!! OLD SPECS: ((None,[]),EInfer [SPLICE]
              EBase exists (Expl)(Impl)[Anon_67; n; Anon_68; 
                    m](ex)x::dll<Anon_67,n>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                    y::dll<Anon_68,m>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 142::ref [x]
                                EXISTS(Anon_69,
                                t: x'::dll<Anon_69,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=t & SPLICE(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_67; n; Anon_68; 
                  m](ex)x::dll<Anon_67,n>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                  y::dll<Anon_68,m>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 142::ref [x]
                              x'::dll<Anon_69,t>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (([0<=t & m+n=t & 0<=n & 0<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=n_4981 & 0<=m_4983 & t_5004=0 & t=2 & -1+n=n_4981 & -1+m=m_4983 & 
  SPLICE(t_5004,m_4983,n_4981)) --> SPLICE(t,m,n),
 (n=0 & m=t & 0<=t) --> SPLICE(t,m,n),
 (0<=m_4983 & 0<=n_4981 & 2+t_5004=t & -1+m=m_4983 & -1+n=n_4981 & 
  SPLICE(t_5004,m_4983,n_4981) & 3<=t) --> SPLICE(t,m,n),
 (0<=m_4983 & 0<=n_4981 & t_5004=0 & t=2 & -1+n=n_4981 & -1+m=m_4983 & 
  SPLICE(t_5004,m_4983,n_4981)) --> SPLICE(t,m,n),
 (m=0 & n=t & 1<=t) --> SPLICE(t,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  SPLIT(n,a,n1,n2)
!!! POST:  a>=1 & n>=a & a=n1 & n=n2+a
!!! PRE :  1<=a & a<=n
!!! OLD SPECS: ((None,[]),EInfer [SPLIT,n,a]
              EBase exists (Expl)(Impl)[p; 
                    n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 97::ref [x]
                                EXISTS(p_168,Anon_59,n1,
                                n2: x'::dll<p_168,n1>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                                res::dll<Anon_59,n2>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (
                                ([0<=n1 & 0<=n2 & SPLIT(n,a,n1,n2)][p=p_168]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  n](ex)x::dll<p,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & a<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 97::ref [x]
                              x'::dll<p_168,n1>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                              res::dll<Anon_59,n2>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (
                              ([n1=a & 0<=n2 & 0<=n & n=a+n2 & 1<=a & 
                                 0<=n1 & a<=n]
                               [p_168=p]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n1=1 & a=1 & -1+n=n2 & 0<=n2) --> SPLIT(n,a,n1,n2),
 ((1<=a_5270 | a_5270<=-1) & SPLIT(n_5216,a_5270,n1_5267,n2_5268) & 0<=n2 & 
  1<=n1 & -1+a=a_5270 & -1+n=n_5216 & 1+n1_5267=n1 & n2_5268=n2 & 
  0<=n_5216) --> SPLIT(n,a,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_24; m; Anon_25; 
                    n](ex)x::dll<Anon_24,m>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                    y::dll<Anon_25,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::ref [x;y]
                                EXISTS(Anon_26,m1,Anon_27,
                                n1: x'::dll<Anon_26,m1>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                                y'::dll<Anon_27,n1>@M[Orig][LHSCase]@ rem br[{566,565}]&
                                (([0<=m1][0<=n1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_24; m; Anon_25; 
                  n](ex)x::dll<Anon_24,m>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                  y::dll<Anon_25,n>@M[Orig][LHSCase]@ rem br[{566,565}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 14::ref [x;y]
                              x'::dll<Anon_26,m1>@M[Orig][LHSCase]@ rem br[{566,565}] * 
                              y'::dll<Anon_27,n1>@M[Orig][LHSCase]@ rem br[{566,565}]&
                              (
                              ([n=m1 & 0<=n][m=n1 & 0<=m][y'=x][y=x']
                               [Anon_25=Anon_26][Anon_24=Anon_27]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 2207 invocations 
7 false contexts at: ( (546,6)  (252,13)  (252,4)  (41,17)  (41,24)  (42,7)  (42,14) )

Total verification time: 4.87 second(s)
	Time spent in main process: 3.76 second(s)
	Time spent in child processes: 1.11 second(s)
