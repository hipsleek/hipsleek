
Processing file "ll_ms.ss"
Parsing ll_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(m,n1,n2)
!!! POST:  n1>=1 & n2>=0 & n1+n2=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[n1; 
                    n2](ex)x::ll<n1>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    y::ll<n2>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                    ([0<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & A(m,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; 
                  n2](ex)x::ll<n1>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  y::ll<n2>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                  ([0<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              EXISTS(m_1141: x::ll<m_1141>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([0<=m_1141 & 0<=n1 & n1+n2=m_1141 & 1<=n1 & 
                                 0<=n2]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=1 & n2=m-1 & 1<=m) --> A(m,n1,n2),
 (n2=n2_1106 & n1=n1_1105+1 & m=m_1128+1 & 0<=n2_1106 & 1<=n1_1105 & 
  1<=m_1128 & A(m_1128,n1_1105,n2_1106)) --> A(m,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
!!! REL :  CL(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&(())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & CL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                    EAssume 48::
                      EXISTS(m_1183: res::ll<m_1183>@M[Orig][LHSCase]@ rem br[{403,402}]&
                      (([n=m_1183 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> CL(m,n),
 ((n=n_1170+1 & m_1169=m-1 & 1<=m & 0<=n_1170 | n=n_1170+1 & m_1169=m-1 & 
  n_1170<=(0-2) & 1<=m) & CL(m_1169,n_1170)) --> CL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! REL :  ASSIGN(n,n1,m)
!!! POST:  m>=0 & n>=0 & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ASSIGN]
              EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n1: x'::ll<n1>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=n1 & ASSIGN(n,n1,m)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              EXISTS(n1_1192: x'::ll<n1_1192>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([n=n1_1192 & 0<=n][0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=n & 0<=n & 0<=m) --> ASSIGN(n,n1,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=1, a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  DEL(m,n,a)
!!! POST:  a>=1 & m>=a & m+1=n
!!! PRE :  1<=a & a<n
!!! OLD SPECS: ((None,[]),EInfer [n,a,DEL]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & DEL(m,n,a)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & (1+a)<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(m_1301: x::ll<m_1301>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([0<=m_1301 & 0<=n & 1+m_1301=n & a<=m_1301 & 
                                 1<=a]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=1 & m=n-1 & 2<=n) --> DEL(m,n,a),
 ((a=v_int_231_1288+1 & m_1287=m-1 & n=n_1266+1 & 1<=m & 0<=n_1266 & 
  1<=v_int_231_1288 | a=v_int_231_1288+1 & m_1287=m-1 & n=n_1266+1 & 
  v_int_231_1288<=(0-1) & 1<=m & 0<=n_1266) & 
  DEL(m_1287,n_1266,v_int_231_1288)) --> DEL(m,n,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & DEL2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(m_1376: res::ll<m_1376>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([m_1376<=n & 0<=n & 0<=m_1376 & (-1+n)<=m_1376]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> DEL2(m,n),
 (m=n-1 & 1<=n) --> DEL2(m,n),
 (m=m_1362+1 & n_1343=n-1 & 0<=m_1362 & 1<=n & 
  DEL2(m_1362,n_1343)) --> DEL2(m,n)]
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
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
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 91::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_18,
                                   m: res::node<m,Anon_18>@M[Orig][]&(
                                   ([FGE(m,v)][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 91::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1474,
                                 m_1475: res::node<m_1475,Anon_1474>@M[Orig][]&
                                 (([(1+v)<=m_1475][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (v<m) --> FGE(m,v),
 (m_1472=m & FGE(m_1472,v)) --> FGE(m,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! REL :  FRONT(res,v)
!!! POST:  v=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FRONT]
              EBase exists (Expl)(Impl)[v; p; m](ex)x::node<v,p>@M[Orig][] * 
                    p::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                    ([x!=null][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(([FRONT(res,v)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; p; m](ex)x::node<v,p>@M[Orig][] * 
                  p::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                  ([x!=null][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              true&(([res=v][0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=v) --> FRONT(res,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  GN(m,n)
!!! POST:  m>=0 & m+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,GN]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::
                                EXISTS(flted_159_106,Anon_14,
                                m: x::node<Anon_14,flted_159_106>@M[Orig][] * 
                                res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (
                                ([null=flted_159_106][0<=m & GN(m,n)]
                                 [x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 27::
                              EXISTS(flted_159_1505,Anon_1506,
                              m_1507: x::node<Anon_1506,flted_159_1505>@M[Orig][] * 
                              res::ll<m_1507>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([1+m_1507=n & 0<=n & 0<=m_1507][x!=null]
                               [null=flted_159_1505]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 1<=n) --> GN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1, n!=0]
!!! REL :  GNN(m,n)
!!! POST:  m>=0 & m+2=n
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & GNN(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              EXISTS(m_1549: res::ll<m_1549>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([2+m_1549=n & 0<=n & 0<=m_1549]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-2 & 2<=n) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  INS(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS,x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & INS(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(m_1621: x::ll<m_1621>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([0<=m_1621 & 0<=n & -1+m_1621=n & 2<=m_1621]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=2 & n=1) --> INS(m,n),
 (n=n_1581+1 & m=m_1608+1 & 1<=n_1581 & 1<=m_1608 & 
  INS(m_1608,n_1581)) --> INS(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 69::
                                EXISTS(n_89,
                                m: x::ll<n_89>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                                res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([n=n_89 & 0<=n_89 & 0<=m & CPY(m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 69::
                              EXISTS(n_1693,
                              m_1694: x::ll<n_1693>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                              res::ll<m_1694>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([n=n_1693 & n=m_1694 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_1644=n-1 & m=m_1657+1 & 1<=n & 0<=m_1657 & 
  CPY(m_1657,n_1644)) --> CPY(m,n),
 (m=0 & n=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  m>=0 & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 83::ref [x]
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & FIL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 83::ref [x]
                              EXISTS(m_1786: res::ll<m_1786>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([m_1786<=n & 0<=n & 0<=m_1786]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_1731=n-1 & m=m_1768 & 1<=n & 0<=m_1768 & FIL(m_1768,n_1731)) --> FIL(m,n),
 (m=m_1761+1 & n_1746=n-1 & 0<=m_1761 & 1<=n & 
  FIL(m_1761,n_1746)) --> FIL(m,n),
 (m=0 & n=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! REL :  RMV(m,n)
!!! POST:  m>=1 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV,x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & RMV(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              EXISTS(m_1916: x::ll<m_1916>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([0<=m_1916 & 0<=n & m_1916<=n & (-1+
                                 n)<=m_1916 & 1<=m_1916]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 2<=n) --> RMV(m,n),
 (m=m_1891+1 & n_1862=n-1 & 1<=m_1891 & 2<=n & 
  RMV(m_1891,n_1862)) --> RMV(m,n),
 (m=1 & n=1) --> RMV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
!!! REL :  RMV2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & RMV2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::
                              EXISTS(m_1992: res::ll<m_1992>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([m_1992<=n & 0<=n & 0<=m_1992 & (-1+n)<=m_1992]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n-1 & 1<=n) --> RMV2(m,n),
 (m=m_1971+1 & n_1957=n-1 & 0<=m_1971 & 1<=n & 
  RMV2(m_1971,n_1957)) --> RMV2(m,n),
 (m=0 & n=0) --> RMV2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & TRAV(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 66::
                              EXISTS(m_2040: x::ll<m_2040>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([n=m_2040 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (n_2016=n-1 & m=m_2023+1 & 1<=n & 0<=m_2023 & 
  TRAV(m_2023,n_2016)) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  PF(n,m)
!!! POST:  n>=0 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,PF]
              EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(n: x'::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=n & PF(n,m)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(n_2067: x'::ll<n_2067>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([1+n_2067=m & 0<=m & 0<=n_2067]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=m-1 & 1<=m) --> PF(n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(m: x'::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & PUF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(m_2081: x'::ll<m_2081>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([0<=m_2081 & 1+n=m_2081 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=m-1 & 1<=m) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! REL :  RF(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RF]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m & RF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              EXISTS(m_2085: x::ll<m_2085>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([n=m_2085 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n & 0<=n) --> RF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
!!! REL :  REV(xs',k,m,n)
!!! POST:  xs'=null & m>=0 & n>=0 & n+m=k
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    ys::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::ref [xs;ys]
                                EXISTS(k: ys'::ll<k>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=k & REV(xs',k,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)xs::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  ys::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 53::ref [xs;ys]
                              EXISTS(k_2145: ys'::ll<k_2145>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([0<=k_2145 & m+n=k_2145 & 0<=m & 0<=n]
                               [null=xs']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n_2116=n-1 & m=m_2117-1 & k=k_2139 & 1<=n & 1<=m_2117 & 0<=k_2139 & 
  REV(xs',k_2139,m_2117,n_2116)) --> REV(xs',k,m,n),
 (n=0 & k=m & xs'=null & 0<=m) --> REV(xs',k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  SN(k,j)
!!! POST:  j>=0 & j+1=k
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,SN]
              EBase exists (Expl)(Impl)[i; 
                    j](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    y::ll<j>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                    ([0<=i][0<=j]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(k: x::ll<k>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=k & SN(k,j)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i; 
                  j](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  y::ll<j>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                  ([0<=i][0<=j]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(k_2177: x::ll<k_2177>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (([0<=k_2177 & 1+j=k_2177 & 0<=j][0<=i]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (j=k-1 & 1<=k) --> SN(k,j)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[i](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=i]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::ref [x]
                                EXISTS(flted_191_102,
                                Anon_16: x'::node<Anon_16,flted_191_102>@M[Orig][]&
                                (([null=flted_191_102][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=i]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              EXISTS(Anon_2196,
                              flted_191_2197: x'::node<Anon_2196,flted_191_2197>@M[Orig][]&
                              (
                              ([1<=i & 0<=i][x'=x & x'!=null]
                               [null=flted_191_2197]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[i](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=i]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(flted_179_104,
                                Anon_15: x'::node<Anon_15,flted_179_104>@M[Orig][]&
                                (([null=flted_179_104][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=i]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              EXISTS(Anon_2227,
                              flted_179_2228: x'::node<Anon_2227,flted_179_2228>@M[Orig][]&
                              (
                              ([x'=x & x'!=null][1<=i & 0<=i]
                               [null=flted_179_2228]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
!!! REL :  SIZEH(res,m,n)
!!! POST:  m>=0 & res=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SIZEH]
              EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&(([SIZEH(res,m,n)]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&(([0<=m & res=m+n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (v_int_58_1007'=res & m_2258=m-1 & 1<=m & SIZEH(v_int_58_1007',m_2258,n+
  1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(([SIZE(res,n)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&(([n=res & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=res & 0<=res) --> SIZE(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
!!! REL :  SPLICE(t,m,n)
!!! POST:  n>=0 & t>=n & t=m+n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLICE]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    y::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 94::ref [x]
                                EXISTS(t: x'::ll<t>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=t & SPLICE(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  y::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 94::ref [x]
                              EXISTS(t_2372: x'::ll<t_2372>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([0<=t_2372 & t_2372=m+n & 0<=m & 0<=n & 
                                 n<=t_2372]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & t=m & 0<=m) --> SPLICE(t,m,n),
 (n_2332=n-1 & m_2333=m-1 & t=t_2348+2 & 1<=m & 1<=n & 0<=t_2348 & 
  SPLICE(t_2348,m_2333,n_2332)) --> SPLICE(t,m,n),
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::ref [x]
                                EXISTS(n1,
                                n2: x'::ll<n1>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                                res::ll<n2>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=n1 & 0<=n2 & SPLIT(n,a,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & a<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 59::ref [x]
                              EXISTS(n1_2476,
                              n2_2477: x'::ll<n1_2476>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                              res::ll<n2_2477>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([a=n1_2476 & a+n2_2477=n & 0<=n & 
                                 0<=n2_2477 & 0<=n1_2476 & 1<=a]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=1 & a=1 & n2=n-1 & 1<=n) --> SPLIT(n,a,n1,n2),
 ((a=a_2461+1 & n2_2459=n2 & n1_2458=n1-1 & n=n_2425+1 & 0<=n2 & 1<=n1 & 
  0<=n_2425 & 1<=a_2461 | a=a_2461+1 & n2_2459=n2 & n1_2458=n1-1 & n=n_2425+
  1 & a_2461<=(0-1) & 0<=n2 & 1<=n1 & 0<=n_2425) & 
  SPLIT(n_2425,a_2461,n1_2458,n2_2459)) --> SPLIT(n,a,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                    y::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m1,
                                n1: x'::ll<m1>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                                y'::ll<n1>@M[Orig][LHSCase]@ rem br[{403,402}]&
                                (([0<=m1][0<=n1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                  y::ll<m>@M[Orig][LHSCase]@ rem br[{403,402}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(m1_2485,
                              n1_2486: x'::ll<m1_2485>@M[Orig][LHSCase]@ rem br[{403,402}] * 
                              y'::ll<n1_2486>@M[Orig][LHSCase]@ rem br[{403,402}]&
                              (
                              ([n=n1_2486 & 0<=n][m=m1_2485 & 0<=m][y=x']
                               [x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1495 invocations 
6 false contexts at: ( (184,13)  (184,4)  (42,4)  (42,11)  (44,4)  (44,11) )

Total verification time: 1.14 second(s)
	Time spent in main process: 0.39 second(s)
	Time spent in child processes: 0.75 second(s)
