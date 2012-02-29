
Processing file "sll_ms.ss"
Parsing sll_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
!!! REL :  ASSIGN(n,n1,m)
!!! POST:  n>=0 & m>=0 & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ASSIGN]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n1: x'::sll<n1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=n1 & ASSIGN(n,n1,m)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              EXISTS(n1_1068: x'::sll<n1_1068>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([n=n1_1068 & 0<=n][0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=n1 & 0<=n1 & 0<=m) --> ASSIGN(n,n1,m)]
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::
                                EXISTS(m: x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & DEL(m,n,a)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & (1+a)<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 53::
                              EXISTS(m_1177: x::sll<m_1177>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([0<=m_1177 & 0<=n & 1+m_1177=n & a<=m_1177 & 
                                 1<=a]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (a=1 & -1+n=m & 1<=m) --> DEL(m,n,a),
 ((1<=v_int_285_1164 | v_int_285_1164<=(0-1)) & 
  DEL(m_1163,n_1142,v_int_285_1164) & 1<=m & -1+n=n_1142 & -1+
  a=v_int_285_1164 & 1+m_1163=m & 0<=n_1142) --> DEL(m,n,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 57::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & DEL2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 57::
                              EXISTS(m_1273: res::sll<m_1273>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([m_1273<=n & 0<=n & 0<=m_1273 & (-1+n)<=m_1273]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=m & 1<=m) --> DEL2(m,n),
 (-1+n=m & 0<=m) --> DEL2(m,n),
 (0<=n_1225 & 1+m_1239=m & -1+n=n_1225 & DEL2(m_1239,n_1225) & 
  1<=m) --> DEL2(m,n),
 (m=0 & n=0) --> DEL2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
!!! REL :  A(x')
!!! POST:  x'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&(([A(x')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              true&(([null=x'][0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (x'=null) --> A(x')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
!!! REL :  EMPT1(res)
!!! POST:  res
!!! PRE :  true
!!! REL :  EMPT2(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [EMPT1,EMPT2]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
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
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
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
!!! REL :  FGE(v,m)
!!! POST:  m>=v
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,FGE]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 89::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_16,
                                   m: res::node<m,Anon_16>@M[Orig][]&(
                                   ([FGE(v,m)][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 89::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1374,
                                 m_1375: res::node<m_1375,Anon_1374>@M[Orig][]&
                                 (([v<=m_1375][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (v<=m) --> FGE(v,m),
 (exists(Anon_1337:m=m_1372 & (1+Anon_1337)<=v & FGE(v,m_1372))) --> FGE(v,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              EXISTS(Anon_1394,q_1395,
                              flted_11_1396: x::node<Anon_1394,q_1395>@M[Orig][] * 
                              q_1395::sll<flted_11_1396>@M[Orig]@ rem br[{388,387}]&
                              (
                              ([1+flted_11_1396=m & 0<=m & 1<=m][x!=null]
                               [res=Anon_1394]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(flted_166_94,v,
                                m: x'::node<v,flted_166_94>@M[Orig][] * 
                                res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (
                                ([null=flted_166_94][0<=m & GN(m,n)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              EXISTS(flted_166_1422,v_1423,
                              m_1424: x'::node<v_1423,flted_166_1422>@M[Orig][] * 
                              res::sll<m_1424>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([1+m_1424=n & 0<=n & 0<=m_1424][x'!=null]
                               [null=flted_166_1422]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+n=m & 0<=m) --> GN(m,n)]
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & GNN(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(m_1466: res::sll<m_1466>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([2+m_1466=n & 0<=n & 0<=m_1466]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-2+n=m & 0<=m) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  GT(m,n)
!!! POST:  m>=0 & m+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,GT]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & GT(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(m_1487: res::sll<m_1487>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([1+m_1487=n & 0<=n & 0<=m_1487]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+n=m & 0<=m) --> GT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & INS(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              EXISTS(m_1583: res::sll<m_1583>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([0<=m_1583 & 0<=n & -1+m_1583=n & 1<=m_1583]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=1 & n=0) --> INS(m,n),
 (1+n=m & 2<=m) --> INS(m,n),
 (0<=n_1524 & 1+m_1538=m & -1+n=n_1524 & INS(m_1538,n_1524) & 
  1<=m) --> INS(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
!!! REL :  INS2(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS2]
              EBase exists (Expl)(Impl)[n; v; 
                    Anon_14](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    vn::node<v,Anon_14>@M[Orig][]&(([0<=n][vn!=null]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & INS2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; v; 
                  Anon_14](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  vn::node<v,Anon_14>@M[Orig][]&(([0<=n][vn!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(m_1691: res::sll<m_1691>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([0<=m_1691 & 0<=n & -1+m_1691=n & 1<=m_1691]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=1 & n=0) --> INS2(m,n),
 (1+n=m & 2<=m) --> INS2(m,n),
 (0<=n_1632 & 1+m_1648=m & -1+n=n_1632 & INS2(m_1648,n_1632) & 
  1<=m) --> INS2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 78::
                                EXISTS(n_79,
                                m: x::sll<n_79>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                                res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([n=n_79 & 0<=n_79 & 0<=m & CPY(m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 78::
                              EXISTS(n_1763,
                              m_1764: x::sll<n_1763>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                              res::sll<m_1764>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([n=n_1763 & n=m_1764 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (0<=n_1714 & 1+m_1727=m & -1+n=n_1714 & 1<=m & 
  CPY(m_1727,n_1714)) --> CPY(m,n),
 (m=0 & n=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  m>=0 & n>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 81::ref [x]
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & FIL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 81::ref [x]
                              EXISTS(m_1856: res::sll<m_1856>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([m_1856<=n & 0<=n & 0<=m_1856]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (0<=n_1801 & m_1838=m & -1+n=n_1801 & FIL(m_1838,n_1801) & 
  0<=m) --> FIL(m,n),
 (1<=m & FIL(m_1831,n_1816) & -1+n=n_1816 & 1+m_1831=m & 
  0<=n_1816) --> FIL(m,n),
 (m=0 & n=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 75::
                                EXISTS(m: x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & TRAV(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 75::
                              EXISTS(m_1904: x::sll<m_1904>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([n=m_1904 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (0<=n_1880 & 1+m_1887=m & -1+n=n_1880 & TRAV(m_1887,n_1880) & 
  1<=m) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
!!! REL :  MRG(m,n1,n2)
!!! POST:  n2>=0 & m>=n2 & m=n1+n2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG]
              EBase exists (Expl)(Impl)[n1; 
                    n2](ex)x1::sll<n1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    x2::sll<n2>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([0<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::ref [x1]
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & MRG(m,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; 
                  n2](ex)x1::sll<n1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  x2::sll<n2>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ([0<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 23::ref [x1]
                              EXISTS(m_1989: res::sll<m_1989>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([0<=m_1989 & 0<=n1 & m_1989=n1+n2 & 0<=n2 & 
                                 n2<=m_1989]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n2=0 & n1=m & 0<=m) --> MRG(m,n1,n2),
 (n1=0 & n2=m & 1<=m) --> MRG(m,n1,n2),
 (2<=n1_1960 & 1<=n2_1961 & m_1982=m & -1+n2=n2_1961 & 1+n1=n1_1960 & 0<=m & 
  MRG(m_1982,n1_1960,n2_1961)) --> MRG(m,n1,n2),
 (1+n1=m & n2=1 & 2<=m) --> MRG(m,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  PF(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,PF]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                EXISTS(n: x'::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=n & PF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              EXISTS(n_2016: x'::sll<n_2016>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([1+n_2016=m & 0<=m & 0<=n_2016]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+m=n & 0<=n) --> PF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(m: x'::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & PUF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(m_2030: x'::sll<m_2030>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([0<=m_2030 & 1+n=m_2030 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+m=n & 0<=n) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! REL :  RF(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RF]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(m: x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=m & RF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(m_2034: x::sll<m_2034>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([n=m_2034 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=m & 0<=m) --> RF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  SN(k,j)
!!! POST:  j>=0 & j+1=k
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,SN]
              EBase exists (Expl)(Impl)[i; 
                    j](ex)x::sll<i>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    y::sll<j>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([0<=i][0<=j]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(k: x'::sll<k>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=k & SN(k,j)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i; 
                  j](ex)x::sll<i>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  y::sll<j>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ([0<=i][0<=j]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              EXISTS(k_2070: x'::sll<k_2070>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (([0<=k_2070 & 1+j=k_2070 & 0<=j][0<=i]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+k=j & 0<=j) --> SN(k,j)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::ref [x]
                                EXISTS(v,r: x'::node<v,r>@M[Orig][]&(
                                ([x'!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 39::ref [x]
                              EXISTS(v_2089,
                              r_2090: x'::node<v_2089,r_2090>@M[Orig][]&(
                              ([1<=n & 0<=n][x'=x & x'!=null][null=r_2090]))&
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::ref [x]
                                EXISTS(v,r: x'::node<v,r>@M[Orig][]&(
                                ([x'!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 34::ref [x]
                              EXISTS(v_2120,
                              r_2121: x'::node<v_2120,r_2121>@M[Orig][]&(
                              ([x'=x & x'!=null][1<=n & 0<=n][null=r_2121]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
!!! REL :  SIZEH(res,m,n)
!!! POST:  m>=0 & m+n=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SIZEH]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&(([SIZEH(res,m,n)]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&(([0<=m & m+n=res]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (0<=m_2151 & res=v_int_61_959' & -1+m=m_2151 & SIZEH(v_int_61_959',m_2151,n-
  -1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,n)
!!! POST:  res>=0 & res=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(([SIZE(res,n)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&(([n=res & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=n & 0<=n) --> SIZE(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ a!=1 | n!=0, n!=0 | a<=1, n!=0 | 1<=a]
!!! REL :  SPLIT(n,a,n1,n2)
!!! POST:  a>=1 & n2>=0 & a=n1 & a+n2=n
!!! PRE :  1<=a & a<=n
!!! OLD SPECS: ((None,[]),EInfer [SPLIT,n,a]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 68::ref [x]
                                EXISTS(n1,
                                n2: x'::sll<n1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                                res::sll<n2>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=n1 & 0<=n2 & SPLIT(n,a,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=a & a<=n]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 68::ref [x]
                              EXISTS(n1_2274,
                              n2_2275: x'::sll<n1_2274>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                              res::sll<n2_2275>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([a=n1_2274 & a+n2_2275=n & 0<=n & 
                                 0<=n2_2275 & 0<=n1_2274 & 1<=a]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=1 & a=1 & -1+n=n2 & 0<=n2) --> SPLIT(n,a,n1,n2),
 ((1<=a_2259 | a_2259<=(0-1)) & 0<=n2 & 1<=n1 & 
  SPLIT(n_2223,a_2259,n1_2256,n2_2257) & -1+n=n_2223 & -1+a=a_2259 & 
  n2_2257=n2 & 1+n1_2256=n1 & 0<=n_2223) --> SPLIT(n,a,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                    y::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(n1,
                                m1: x'::sll<n1>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                                y'::sll<m1>@M[Orig][LHSCase]@ rem br[{388,387}]&
                                (([0<=n1][0<=m1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                  y::sll<m>@M[Orig][LHSCase]@ rem br[{388,387}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              EXISTS(n1_2283,
                              m1_2284: x'::sll<n1_2283>@M[Orig][LHSCase]@ rem br[{388,387}] * 
                              y'::sll<m1_2284>@M[Orig][LHSCase]@ rem br[{388,387}]&
                              (
                              ([n=m1_2284 & 0<=n][m=n1_2283 & 0<=m][y=x']
                               [x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1324 invocations 
6 false contexts at: ( (193,13)  (193,4)  (44,4)  (44,11)  (46,4)  (46,11) )

Total verification time: 0.92 second(s)
	Time spent in main process: 0.35 second(s)
	Time spent in child processes: 0.57 second(s)
