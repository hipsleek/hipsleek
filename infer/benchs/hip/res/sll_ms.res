
Processing file "sll_ms.ss"
Parsing sll_ms.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
!!! REL :  CL(m,n)
!!! POST:  m>=1 & m=n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&0<=n&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 60::
                                                         true&res=null&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 61::
                                                         EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                                         CL(m,n)&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 62::
                                                         true&true&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&0<=n&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 60::
                                                       true&res=null & n=0&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&1<=n & MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 61::
                                                       res::sll<m>@M[Orig][LHSCase]&
                                                       m>=1 & m=n & 0<n&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           n<0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 62::
                                                       true&n<0&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (n=1 & m=1) --> CL(m,n),
 (1+m_1066=m & 1<=m & CL(m_1066,n_1067) & 2<=n & 1+n_1067=n) --> CL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
( [(224::,0 ); (224::,0 )]) :sll_ms.ss:253: 13: bind: node  v_node_253_750'::node<val_253_751',next_253_752'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):sll_ms.ss:253: 13:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(224::,0 ); (224::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    15.1 v_node_253_750'=null & v_node_253_750'=q_1102 |-  v_node_253_750'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [n,DEL,x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::ref [x]
                                EXISTS(m: x'::sll<m>@M[Orig][LHSCase]&
                                DEL(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 50::ref [x]
                              x'::sll<m>@M[Orig][LHSCase]&DEL(m,n) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int result FAIL-1

Checking procedure delete2$node~int... 
!!! REL :  DEL2(m,n)
!!! POST:  m>=0 & (m+1)>=n & n>=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                DEL2(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              res::sll<m>@M[Orig][LHSCase]&m>=0 & (m+1)>=n & 
                              n>=m & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=1 & n=1 | n=m & 2<=m) --> DEL2(m,n),
 (m=0 & n=1 | -1+n=m & 1<=m) --> DEL2(m,n),
 (1+m_1221=m & 1<=m & DEL2(m_1221,n_1207) & 1<=n & 1+n_1207=n) --> DEL2(m,n),
 (n=0 & m=0) --> DEL2(m,n)]
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 81::
                                
                                true&res=null&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_15,
                                   m: res::node<m,Anon_15>@M[Orig]&FGE(v,m)&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 81::
                              
                              true&res=null & 0<=n&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_15>@M[Orig]&m>=v & 0<=n&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (v<=m) --> FGE(v,m),
 (exists(Anon_1314:m_1349=m & (1+Anon_1314)<=v & FGE(v,m_1349))) --> FGE(v,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x,res]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              x::node<Anon_1365,q_1366>@M[Orig] * 
                              q_1366::sll<flted_16_1364>@M[Orig]&
                              m=flted_16_1364+1 & res=Anon_1365 & 0<=m&
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
!!! POST:  m>=0 & m+1=n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [x,GN]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::ref [x]
                                EXISTS(flted_142_95,v,
                                m: x'::node<v,flted_142_95>@M[Orig] * 
                                res::sll<m>@M[Orig][LHSCase]&
                                flted_142_95=null & GN(m,n)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              x'::node<v,flted_142_95>@M[Orig] * 
                              res::sll<m>@M[Orig][LHSCase]&
                              flted_142_95=null & m>=0 & m+1=n & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=1 | -1+n=m & 1<=m) --> GN(m,n)]
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                GNN(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&2<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              res::sll<m>@M[Orig][LHSCase]&m>=0 & m+2=n & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(flted_16_1428:m=0 & n=2 | -2+n=m & flted_16_1428=m & 
  1<=m)) --> GNN(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  GT(m,n)
!!! POST:  m>=0 & m+1=n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [x,GT]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                GT(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & 1<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              res::sll<m>@M[Orig][LHSCase]&m>=0 & m+1=n & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & n=1 | -1+n=m & 1<=m) --> GT(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                INS(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              res::sll<m>@M[Orig][LHSCase]&n>=0 & n+1=m & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & m=1) --> INS(m,n),
 (m=2 & n=1 | 1+n=m & 3<=m) --> INS(m,n),
 (1+m_1505=m & 1<=m & INS(m_1505,n_1491) & 1<=n & 1+n_1491=n) --> INS(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
!!! REL :  INS2(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [INS2]
              EBase exists (Expl)(Impl)[n; v; 
                    Anon_14](ex)x::sll<n>@M[Orig][LHSCase] * 
                    vn::node<v,Anon_14>@M[Orig]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 44::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                INS2(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; v; 
                  Anon_14](ex)x::sll<n>@M[Orig][LHSCase] * 
                  vn::node<v,Anon_14>@M[Orig]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 44::
                              res::sll<m>@M[Orig][LHSCase]&n>=0 & n+1=m & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & m=1) --> INS2(m,n),
 (m=2 & n=1 | 1+n=m & 3<=m) --> INS2(m,n),
 (1+m_1614=m & 1<=m & INS2(m_1614,n_1598) & 1<=n & 1+n_1598=n) --> INS2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 70::
                                EXISTS(n_83,
                                m: x::sll<n_83>@M[Orig][LHSCase] * 
                                res::sll<m>@M[Orig][LHSCase]&CPY(m,n) & 
                                n_83=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 70::
                              x::sll<n_83>@M[Orig][LHSCase] * 
                              res::sll<m>@M[Orig][LHSCase]&n_83=n & m>=0 & 
                              m=n & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(flted_16_1674:exists(n_83:(n=1 & n_1679=0 & 1+m_1692=m & 1<=m | 1+
  flted_16_1674=n_83 & n=n_83 & 1+n_1679=n_83 & 1+m_1692=m & 1<=m & 
  2<=n_83) & CPY(m_1692,n_1679)))) --> CPY(m,n),
 (n=0 & m=0) --> CPY(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 73::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                FIL(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 73::
                              res::sll<m>@M[Orig][LHSCase]&m>=0 & m=n & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (1+m_1786=m & 1<=m & FIL(m_1786,n_1772) & 1<=n & 1+n_1772=n) --> FIL(m,n),
 (n=0 & m=0) --> FIL(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(m,n)
!!! POST:  m>=0 & m=n
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 67::
                                EXISTS(m: x::sll<m>@M[Orig][LHSCase]&
                                TRAV(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 67::
                              x::sll<m>@M[Orig][LHSCase]&m>=0 & m=n & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (1+m_1836=m & 1<=m & TRAV(m_1836,n_1829) & 1<=n & 1+n_1829=n) --> TRAV(m,n),
 (n=0 & m=0) --> TRAV(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
!!! REL :  MRG(m,n1,n2)
!!! POST:  n1>=0 & m>=n1 & m=n2+n1
!!! PRE :  0<=n1 & 0<=n2
!!! OLD SPECS: ((None,[]),EInfer [MRG]
              EBase exists (Expl)(Impl)[n1; 
                    n2](ex)x1::sll<n1>@M[Orig][LHSCase] * 
                    x2::sll<n2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                EXISTS(m: res::sll<m>@M[Orig][LHSCase]&
                                MRG(m,n1,n2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; 
                  n2](ex)x1::sll<n1>@M[Orig][LHSCase] * 
                  x2::sll<n2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=n1 & 0<=n2 & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 21::
                              res::sll<m>@M[Orig][LHSCase]&n1>=0 & m>=n1 & 
                              m=n2+n1 & 0<=n1 & 0<=n2&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=n1 & 0<=n1 & n2=0) --> MRG(m,n1,n2),
 (n1=0 & n2=m & 1<=m) --> MRG(m,n1,n2),
 (-1+n1_1903=n1 & 1+n2_1904=n2 & -1+m=n1 & -1+m_1922=n1 & 1<=n2 & 0<=n1 & 
  MRG(m_1922,n1_1903,n2_1904)) --> MRG(m,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  PF(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  1<=m
!!! OLD SPECS: ((None,[]),EInfer [x,PF]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(n: x'::sll<n>@M[Orig][LHSCase]&
                                PF(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & 1<=m & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::sll<n>@M[Orig][LHSCase]&n>=0 & n+1=m & 
                              0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n=0 & m=1 | -1+m=n & 1<=n) --> PF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(m,n)
!!! POST:  n>=0 & n+1=m
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(m: x'::sll<m>@M[Orig][LHSCase]&
                                PUF(m,n)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              x'::sll<m>@M[Orig][LHSCase]&n>=0 & n+1=m & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (1+n=m & 1<=m) --> PUF(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! REL :  SN(k,j)
!!! POST:  j>=0 & j+1=k
!!! PRE :  0<=j
!!! OLD SPECS: ((None,[]),EInfer [x,SN]
              EBase exists (Expl)(Impl)[i; 
                    j](ex)x::sll<i>@M[Orig][LHSCase] * 
                    y::sll<j>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::ref [x]
                                EXISTS(k: x'::sll<k>@M[Orig][LHSCase]&
                                SN(k,j)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[i; j](ex)x::sll<i>@M[Orig][LHSCase] * 
                  y::sll<j>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & 0<=j & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              x'::sll<k>@M[Orig][LHSCase]&j>=0 & j+1=k & 
                              0<=i & 0<=j&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (0<=j & -1+k=j) --> SN(k,j)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [x]
                                EXISTS(flted_187_90,
                                v: x'::node<v,flted_187_90>@M[Orig]&
                                flted_187_90=null&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [x]
                              x'::node<v,flted_187_90>@M[Orig]&
                              n=flted_16_2012+1 & x=x' & flted_187_90=null & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(flted_165_92,
                                v: x'::node<v,flted_165_92>@M[Orig]&
                                flted_165_92=null&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              x'::node<v,flted_165_92>@M[Orig]&
                              n=flted_16_2037+1 & x=x' & flted_165_92=null & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
!!! REL :  SIZEH(res,m,n)
!!! POST:  m>=0 & res=n+m
!!! PRE :  0<=m
!!! OLD SPECS: ((None,[]),EInfer [SIZEH]
              EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::ref [n]
                                true&SIZEH(res,m,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::sll<m>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=m & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 7::ref [n]
                              true&m>=0 & res=n+m & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m=0 & res=n) --> SIZEH(res,m,n),
 (1+m_2074=m & v_int_50_951'=res & 1<=m & SIZEH(v_int_50_951',m_2074,n-
  -1)) --> SIZEH(res,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
!!! REL :  SIZE(res,n)
!!! POST:  n>=0 & n=res
!!! PRE :  0<=n
!!! OLD SPECS: ((None,[]),EInfer [SIZE]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                true&SIZE(res,n)&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              true&n>=0 & n=res & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (res=n & 0<=n) --> SIZE(res,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
!!! REL :  SPLIT(n,n1,n2)
!!! POST:  n1>=1 & n2>=1 & n1+n2=n
!!! PRE :  2<=n
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                    0<a & a<n&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::ref [x]
                                EXISTS(n1,n2: x'::sll<n1>@M[Orig][LHSCase] * 
                                res::sll<n2>@M[Orig][LHSCase]&SPLIT(n,n1,n2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&2<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 84::ref [x]
                              x'::sll<n1>@M[Orig][LHSCase] * 
                              res::sll<n2>@M[Orig][LHSCase]&n1>=1 & n2>=1 & 
                              n1+n2=n & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (n1=1 & 1+n2=n & 2<=n) --> SPLIT(n,n1,n2),
 (n2=n2_2178 & 1+n1_2177=n1 & 1<=n1 & 0<=n2_2178 & 
  SPLIT(n_2146,n1_2177,n2_2178) & 1+n_2146=n & exists(a:(1+a)<=n & 
  2<=a)) --> SPLIT(n,n1,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! REL :  SWAP(m,n,m1,n1)
!!! POST:  m>=0 & n>=0 & m=n1 & n=m1
!!! PRE :  0<=m & 0<=n
!!! OLD SPECS: ((None,[]),EInfer [SWAP]
              EBase exists (Expl)(Impl)[n; 
                    m](ex)x::sll<n>@M[Orig][LHSCase] * 
                    y::sll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m1,n1: x'::sll<n1>@M[Orig][LHSCase] * 
                                y'::sll<m1>@M[Orig][LHSCase]&SWAP(m,n,m1,n1)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; m](ex)x::sll<n>@M[Orig][LHSCase] * 
                  y::sll<m>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&0<=m & 0<=n & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::sll<n1>@M[Orig][LHSCase] * 
                              y'::sll<m1>@M[Orig][LHSCase]&m>=0 & n>=0 & 
                              m=n1 & n=m1 & 0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m1=n & n1=m & 0<=m & 0<=n) --> SWAP(m,n,m1,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1005 invocations 
20 false contexts at: ( (170,13)  (170,4)  (351,10)  (351,6)  (350,10)  (350,6)  (36,17)  (36,24)  (37,7)  (37,14)  (298,4)  (298,11)  (303,4)  (303,11)  (302,10)  (302,4)  (301,9)  (301,13)  (301,4)  (301,4) )

Total verification time: 1.84 second(s)
	Time spent in main process: 1.18 second(s)
	Time spent in child processes: 0.66 second(s)
