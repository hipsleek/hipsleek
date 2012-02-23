
Processing file "ll_ms.ss"
Parsing ll_ms.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! REL :  A(m,n1,n2)
!!! POST:  n1>=1 & m>=n1 & m=n2+n1
!!! PRE :  1<=n1 & 0<=n2
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n1; 
                    n2](ex)x::ll<n1>@M[Orig][LHSCase]@ rem br[{401}] * 
                    y::ll<n2>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                    ([null!=x][0<=n1 & 0!=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & A(m,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; 
                  n2](ex)x::ll<n1>@M[Orig][LHSCase]@ rem br[{401}] * 
                  y::ll<n2>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                  ([x!=null][1<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n1][0<=n2]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 23::
                              x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=m & 0<=n1 & m=n1+n2 & 0<=n2 & 1<=n1 & 
                                 n1<=m]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n1=1 & -1+m=n2 & 0<=n2) --> A(m,n1,n2),
 (n2_1118=n2 & 1+m_1140=m & 1+n1_1117=n1 & 0<=n2 & 2<=n1 & 2<=m & 
  A(m_1140,n1_1117,n2_1118)) --> A(m,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! REL :  ASSIGN(n,n1,m)
!!! POST:  m>=0 & n1>=0 & n1=n
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [ASSIGN]
              EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n1: x'::ll<n1>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=n1 & ASSIGN(n,n1,m)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              x'::ll<n1>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([n=n1 & 0<=n1][0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=n1 & 0<=n1 & 0<=m) --> ASSIGN(n,n1,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1, n!=0, n!=0]
!!! REL :  DEL(m,n)
!!! POST:  n>=2 & n=m+1
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,DEL]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & DEL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=m & 0<=n & -1+n=m & 2<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 1<=m) --> DEL(m,n),
 (DEL(m_1293,n_1272) & 1<=m & 1+m_1293=m & -1+n=n_1272 & 
  0<=n_1272) --> DEL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & DEL2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([m<=n & 0<=n & 0<=m & (-1+n)<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=0) --> DEL2(m,n),
 (-1+n=m & 0<=m) --> DEL2(m,n),
 (DEL2(m_1367,n_1348) & 1<=m & 1+m_1367=m & -1+n=n_1348 & 
  0<=n_1348) --> DEL2(m,n)]
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
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
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 91::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_18,
                                   m: res::node<m,Anon_18>@M[Orig][]&(
                                   ([FGE(m,v)][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 91::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_18>@M[Orig][]&(
                                 ([(1+v)<=m][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ ((1+v)<=m) --> FGE(m,v),
 (exists(Anon_1441:m=m_1476 & Anon_1441<=v & FGE(m_1476,v))) --> FGE(m,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! REL :  FRONT(res,v)
!!! POST:  res=v
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FRONT]
              EBase exists (Expl)(Impl)[v; p; m](ex)x::node<v,p>@M[Orig][] * 
                    p::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                    ([x!=null][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(([FRONT(res,v)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; p; m](ex)x::node<v,p>@M[Orig][] * 
                  p::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                  ([x!=null][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              true&(([v=res][0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (v=res) --> FRONT(res,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(m,n)
!!! POST:  n>=1 & n=m+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                    (([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::
                                EXISTS(flted_151_107,Anon_14,
                                m: x::node<Anon_14,flted_151_107>@M[Orig][] * 
                                res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (
                                ([null=flted_151_107][0<=m & GN(m,n)]
                                 [x!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                  (([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 27::
                              x::node<Anon_14,flted_151_107>@M[Orig][] * 
                              res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (
                              ([0<=m & 0<=n & -1+n=m & 1<=n][x!=null]
                               [flted_151_107=null]))&
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                    (([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & GNN(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                  (([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([0<=m & 0<=n & -2+n=m & 2<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-2+n=m & 0<=m) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(m,n)
!!! POST:  m>=2 & m=n+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                    (([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & INS(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                  (([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=m & 0<=n & -1+m=n & 2<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=2 & n=1) --> INS(m,n),
 (1<=n_1579 & 1+m_1604=m & -1+n=n_1579 & INS(m_1604,n_1579) & 
  2<=m) --> INS(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 69::
                                EXISTS(n_89,
                                m: x::ll<n_89>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                                res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([n=n_89 & 0<=n_89 & 0<=m & CPY(m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 69::
                              x::ll<n_89>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                              res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([m=n & m=n_89 & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=n_1639 & 1+m_1652=m & -1+n=n_1639 & 1<=m & 
  CPY(m_1652,n_1639)) --> CPY(m,n),
 (m=0 & n=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  m>=0 & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 83::ref [x]
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & FIL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 83::ref [x]
                              res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([m<=n & 0<=n & 0<=m]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=n_1724 & m_1761=m & -1+n=n_1724 & FIL(m_1761,n_1724) & 
  0<=m) --> FIL(m,n),
 (1<=m & FIL(m_1754,n_1739) & -1+n=n_1739 & 1+m_1754=m & 
  0<=n_1739) --> FIL(m,n),
 (m=0 & n=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! REL :  RMV(m,n)
!!! POST:  (m+1)>=n & m>=1 & n>=m
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [RMV]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                    (([null!=x][0<=n & 0!=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & RMV(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{401}]&
                  (([x!=null][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=m & 0<=n & m<=n & 1<=m & (-1+n)<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 1<=m) --> RMV(m,n),
 (RMV(m_1883,n_1854) & 2<=m & 1+m_1883=m & 1+n_1854=n & 2<=n) --> RMV(m,n),
 (m=1 & n=1) --> RMV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
!!! REL :  RMV2(m,n)
!!! POST:  (m+1)>=n & m>=0 & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::
                                EXISTS(m: res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & RMV2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 76::
                              res::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([m<=n & 0<=n & (-1+n)<=m & 0<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 0<=m) --> RMV2(m,n),
 (RMV2(m_1957,n_1943) & 1<=m & -1+n=n_1943 & 1+m_1957=m & 
  0<=n_1943) --> RMV2(m,n),
 (m=0 & n=0) --> RMV2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & TRAV(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 66::
                              x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([n=m & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (0<=n_2001 & 1+m_2008=m & -1+n=n_2001 & TRAV(m_2008,n_2001) & 
  1<=m) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(n,m)
!!! POST:  m>=1 & m=n+1
!!! PRE :  1<=m
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{401}]&
                    (([null!=x][0<=m & 0!=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(n: x'::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=n & PF(n,m)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{401}]&
                  (([x!=null][1<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              x'::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=n & 0<=m & -1+m=n & 1<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+m=n & 0<=n) --> PF(n,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(m: x'::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & PUF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=m & 0<=n & -1+m=n & 1<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+m=n & 0<=n) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! REL :  RF(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [RF]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                EXISTS(m: x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m & RF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([n=m & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=m & 0<=m) --> RF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
!!! REL :  REV(xs',k,m,n)
!!! POST:  m>=0 & k>=m & xs'=null & k=n+m
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)xs::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                    ys::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::ref [xs;ys]
                                EXISTS(k: ys'::ll<k>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=k & REV(xs',k,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)xs::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                  ys::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 53::ref [xs;ys]
                              ys'::ll<k>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (
                              ([0<=k & 0<=n & k=m+n & 0<=m & m<=k][null=xs']))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=n_2097 & -1+m_2098=m & k_2120=k & -1+n=n_2097 & 0<=m & 
  REV(xs',k_2120,m_2098,n_2097) & 0<=k & 
  exists(xs:xs!=null)) --> REV(xs',k,m,n),
 (m=k & n=0 & xs'=null & 0<=k) --> REV(xs',k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(k,j)
!!! POST:  k>=1 & k=j+1
!!! PRE :  0<=j
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[i; 
                    j](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{401}] * 
                    y::ll<j>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                    ([null!=x][0<=i & 0!=i][0<=j]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(k: x::ll<k>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=k & SN(k,j)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i; 
                  j](ex)x::ll<i>@M[Orig][LHSCase]@ rem br[{401}] * 
                  y::ll<j>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                  ([x!=null][1<=i][0<=j]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=j]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              x::ll<k>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=k & 0<=j & -1+k=j & 1<=k][0<=i]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+k=j & 0<=j) --> SN(k,j)]
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
              EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&(([SIZEH(res,m,n)]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&(([0<=m & res=m+n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (0<=m_2249 & res=v_int_55_1019' & -1+m=m_2249 & 
  SIZEH(v_int_55_1019',m_2249,n--1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(([SIZE(res,n)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&(([res=n & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=n & 0<=n) --> SIZE(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
!!! REL :  SPLICE(t,m,n)
!!! POST:  m>=0 & n>=0 & m+n=t
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [SPLICE]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                    y::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 94::ref [x]
                                EXISTS(t: x'::ll<t>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=t & SPLICE(t,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                  y::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 94::ref [x]
                              x'::ll<t>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                              ([0<=t & m+n=t & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & m=t & 0<=t) --> SPLICE(t,m,n),
 (0<=m_2324 & 0<=n_2323 & 2+t_2339=t & -1+n=n_2323 & -1+m=m_2324 & 2<=t & 
  SPLICE(t_2339,m_2324,n_2323)) --> SPLICE(t,m,n),
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
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::ref [x]
                                EXISTS(n1,
                                n2: x'::ll<n1>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                                res::ll<n2>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=n1 & 0<=n2 & SPLIT(n,a,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & a<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 59::ref [x]
                              x'::ll<n1>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                              res::ll<n2>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (
                              ([n1=a & 0<=n2 & 0<=n & n=a+n2 & 1<=a & 
                                 0<=n1 & a<=n]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n1=1 & a=1 & -1+n=n2 & 0<=n2) --> SPLIT(n,a,n1,n2),
 ((1<=a_2451 | a_2451<=-1) & 0<=n2 & 1<=n1 & 
  SPLIT(n_2415,a_2451,n1_2448,n2_2449) & -1+n=n_2415 & -1+a=a_2451 & 
  n2_2449=n2 & 1+n1_2448=n1 & 0<=n_2415) --> SPLIT(n,a,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! REL :  SWAP(m,n,m1,n1)
!!! POST:  n1>=0 & m1>=0 & n1=n & m1=m
!!! PRE :  0<=n & 0<=m
!!! OLD SPECS: ((None,[]),EInfer [SWAP]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                    y::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m1,
                                n1: x'::ll<m1>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                                y'::ll<n1>@M[Orig][LHSCase]@ rem br[{402,401}]&
                                (([0<=m1 & 0<=n1 & SWAP(m,n,m1,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)x::ll<n>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                  y::ll<m>@M[Orig][LHSCase]@ rem br[{402,401}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::ll<m1>@M[Orig][LHSCase]@ rem br[{402,401}] * 
                              y'::ll<n1>@M[Orig][LHSCase]@ rem br[{402,401}]&
                              (([m=m1 & 0<=m][n=n1 & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=m1 & n=n1 & 0<=m1 & 0<=n1) --> SWAP(m,n,m1,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1338 invocations 
6 false contexts at: ( (175,13)  (175,4)  (41,17)  (41,24)  (42,7)  (42,14) )

Total verification time: 3.42 second(s)
	Time spent in main process: 2.25 second(s)
	Time spent in child processes: 1.17 second(s)
