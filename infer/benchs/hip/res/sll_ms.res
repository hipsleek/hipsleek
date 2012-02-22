
Processing file "sll_ms.ss"
Parsing sll_ms.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
!!! REL :  CL(m,n)
!!! POST:  n>=1 & n=m
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&(([0<=n]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 60::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 61::
                                                         EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                                         (
                                                         ([0<=m & CL(m,n)]))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 62::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(([0<=n]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 60::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop][1<=n]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 61::
                                                       res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                                       (
                                                       ([m=n & 0<=m & 1<=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 62::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (m=1 & n=1) --> CL(m,n),
 (1<=n_1067 & 1+m_1066=m & -1+n=n_1067 & 1<=m & 
  CL(m_1066,n_1067)) --> CL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1 | x=null, n!=0 | x!=null, n!=0 | x!=null]
!!! REL :  DEL(m,n)
!!! POST:  n>=2 & n=m+1
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,DEL,x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::ref [x]
                                EXISTS(m: x'::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & DEL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 50::ref [x]
                              x'::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & 0<=n & -1+n=m & 2<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 1<=m) --> DEL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  (m+1)>=n & m>=0 & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & DEL2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([m<=n & 0<=n & (-1+n)<=m & 0<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=m & 1<=m) --> DEL2(m,n),
 (-1+n=m & 0<=m) --> DEL2(m,n),
 (0<=n_1240 & 1+m_1254=m & -1+n=n_1240 & DEL2(m_1254,n_1240) & 
  1<=m) --> DEL2(m,n),
 (m=0 & n=0) --> DEL2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(v,m)
!!! POST:  m>=v
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,FGE]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 81::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_15,
                                   m: res::node<m,Anon_15>@M[Orig][]&(
                                   ([FGE(v,m)][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 81::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_15>@M[Orig][]&(
                                 ([v<=m][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (v<=m) --> FGE(v,m),
 (exists(Anon_1352:m=m_1387 & (1+Anon_1352)<=v & FGE(v,m_1387))) --> FGE(v,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x,res]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              x::node<Anon_1408,q_1409>@M[Orig][]&(
                              ([1<=m & 0<=m][x!=null][Anon_1408=res]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  GN(m,n)
!!! POST:  n>=1 & n=m+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [x,GN]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::ref [x]
                                EXISTS(flted_142_95,v,
                                m: x'::node<v,flted_142_95>@M[Orig][] * 
                                res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_142_95][0<=m & GN(m,n)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n][x!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              x'::node<v,flted_142_95>@M[Orig][] * 
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=m & 0<=n & -1+n=m & 1<=n][x'!=null]
                               [flted_142_95=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 0<=m) --> GN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1, n!=0]
!!! REL :  GNN(m,n)
!!! POST:  n>=2 & n=m+2
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & GNN(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & 0<=n & -2+n=m & 2<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-2+n=m & 0<=m) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  GT(m,n)
!!! POST:  n>=1 & n=m+1
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [x,GT]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & GT(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n][x!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 35::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & 0<=n & -1+n=m & 1<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+n=m & 0<=m) --> GT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & INS(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & 0<=n & -1+m=n & 1<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=1 & n=0) --> INS(m,n),
 (1+n=m & 2<=m) --> INS(m,n),
 (0<=n_1537 & 1+m_1551=m & -1+n=n_1537 & INS(m_1551,n_1537) & 
  1<=m) --> INS(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
!!! REL :  INS2(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [INS2]
              EBase exists (Expl)(Impl)[n; v; 
                    Anon_14](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    vn::node<v,Anon_14>@M[Orig][]&(([0<=n][vn!=null]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 44::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & INS2(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; v; 
                  Anon_14](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  vn::node<v,Anon_14>@M[Orig][]&(([0<=n][vn!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 44::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & 0<=n & -1+m=n & 1<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=1 & n=0) --> INS2(m,n),
 (1+n=m & 2<=m) --> INS2(m,n),
 (0<=n_1648 & 1+m_1664=m & -1+n=n_1648 & INS2(m_1664,n_1648) & 
  1<=m) --> INS2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 70::
                                EXISTS(n_83,
                                m: x::sll<n_83>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([n=n_83 & 0<=n_83 & 0<=m & CPY(m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 70::
                              x::sll<n_83>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([n=m & n=n_83 & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=0) --> CPY(m,n),
 (0<=n_1733 & 1+m_1746=m & -1+n=n_1733 & 1<=m & 
  CPY(m_1746,n_1733)) --> CPY(m,n),
 (m=0 & n=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  n>=0 & n=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 73::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & FIL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 73::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([m=n & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (FIL(m_1844,n_1830) & 1<=m & -1+n=n_1830 & 1+m_1844=m & 
  0<=n_1830) --> FIL(m,n),
 (m=0 & n=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 67::
                                EXISTS(m: x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & TRAV(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 67::
                              x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                              ([n=m & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (0<=n_1888 & 1+m_1895=m & -1+n=n_1888 & TRAV(m_1895,n_1888) & 
  1<=m) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
!!! REL :  MRG(m,n1,n2)
!!! POST:  n2>=0 & n1>=0 & n2+n1=m
!!! PRE :  0<=n2 & 0<=n1
!!! OLD SPECS: ((None,[]),EInfer [MRG]
              EBase exists (Expl)(Impl)[n1; 
                    n2](ex)x1::sll<n1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    x2::sll<n2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([0<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & MRG(m,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; 
                  n2](ex)x1::sll<n1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  x2::sll<n2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ([0<=n1][0<=n2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n2][0<=n1]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 21::
                              res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & n1+n2=m & 0<=n2 & 0<=n1]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n1=m & n2=0 & 0<=m) --> MRG(m,n1,n2),
 (n2=m & n1=0 & 1<=m) --> MRG(m,n1,n2),
 (2<=n1_1966 & 1<=n2_1967 & m_1986=n1_1966 & m=n1_1966 & -1+n2=n2_1967 & 1+
  n1=n1_1966 & MRG(m_1986,n1_1966,n2_1967)) --> MRG(m,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  PF(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  1<=m
!!! OLD SPECS: ((None,[]),EInfer [x,PF]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(n: x'::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=n & PF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=m][x!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=n & 0<=m & -1+m=n & 1<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+m=n & 0<=n) --> PF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  m>=1 & m=n+1
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(m: x'::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & PUF(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              x'::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m & 0<=n & -1+m=n & 1<=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+m=n & 0<=n) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  SN(k,j)
!!! POST:  k>=1 & k=j+1
!!! PRE :  0<=j
!!! OLD SPECS: ((None,[]),EInfer [x,SN]
              EBase exists (Expl)(Impl)[i; 
                    j](ex)x::sll<i>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    y::sll<j>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([0<=i][0<=j]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::ref [x]
                                EXISTS(k: x'::sll<k>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=k & SN(k,j)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i; 
                  j](ex)x::sll<i>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  y::sll<j>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ([0<=i][0<=j]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=j][x!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              x'::sll<k>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=k & 0<=j & -1+k=j & 1<=k][0<=i]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (-1+k=j & 0<=j) --> SN(k,j)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [x]
                                EXISTS(flted_187_90,
                                v: x'::node<v,flted_187_90>@M[Orig][]&(
                                ([null=flted_187_90][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [x]
                              x'::node<v,flted_187_90>@M[Orig][]&(
                              ([flted_187_90=null][1<=n & 0<=n]
                               [x'=x & x!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(flted_165_92,
                                v: x'::node<v,flted_165_92>@M[Orig][]&(
                                ([null=flted_165_92][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([x!=null][MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              x'::node<v,flted_165_92>@M[Orig][]&(
                              ([flted_165_92=null][1<=n & 0<=n]
                               [x'=x & x!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
!!! REL :  SIZEH(res,m,n)
!!! POST:  m>=0 & res=n+m
!!! PRE :  0<=m
!!! OLD SPECS: ((None,[]),EInfer [SIZEH]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&(([SIZEH(res,m,n)]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&(([0<=m & res=m+n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (0<=m_2146 & res=v_int_50_951' & -1+m=m_2146 & SIZEH(v_int_50_951',m_2146,n-
  -1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&(([SIZE(res,n)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&(([res=n & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=n & 0<=n) --> SIZE(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
!!! REL :  SPLIT(n,n1,n2)
!!! POST:  n1>=1 & n>=(1+n1) & n=n2+n1
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{383}]&
                    (([(1+a)<=n & 1<=a][null!=x]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::ref [x]
                                EXISTS(n1,
                                n2: x'::sll<n1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                res::sll<n2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=n1 & 0<=n2 & SPLIT(n,n1,n2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 84::ref [x]
                              x'::sll<n1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              res::sll<n2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=n2 & 0<=n & n=n1+n2 & 1<=n1 & 0<=n1 & (1+
                                 n1)<=n]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n1=1 & -1+n=n2 & 1<=n2) --> SPLIT(n,n1,n2),
 (exists(a:n2_2254=n2 & 1+n1_2253=n1 & -1+n=n_2222 & 
  SPLIT(n_2222,n1_2253,n2_2254) & 0<=n2 & 1<=n1 & 2<=a & 
  a<=n_2222)) --> SPLIT(n,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! REL :  SWAP(m,n,m1,n1)
!!! POST:  m1>=0 & n1>=0 & m1=n & n1=m
!!! PRE :  0<=n & 0<=m
!!! OLD SPECS: ((None,[]),EInfer [SWAP]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    y::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m1,
                                n1: x'::sll<n1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                y'::sll<m1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=n1 & 0<=m1 & SWAP(m,n,m1,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  m](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  y::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ([0<=n][0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=n][0<=m]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::sll<n1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              y'::sll<m1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([m=n1 & 0<=m][n=m1 & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=n1 & n=m1 & 0<=n1 & 0<=m1) --> SWAP(m,n,m1,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1794 invocations 
20 false contexts at: ( (170,13)  (170,4)  (351,10)  (351,6)  (350,10)  (350,6)  (36,17)  (36,24)  (37,7)  (37,14)  (298,4)  (298,11)  (303,4)  (303,11)  (302,10)  (302,4)  (301,9)  (301,13)  (301,4)  (301,4) )

Total verification time: 4.31 second(s)
	Time spent in main process: 2.89 second(s)
	Time spent in child processes: 1.42 second(s)
