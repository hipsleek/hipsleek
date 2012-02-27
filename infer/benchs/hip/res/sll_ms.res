
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
                                                       EXISTS(m_1080: 
                                                       res::sll<m_1080>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                                       (
                                                       ([n=m_1080 & 
                                                          0<=m_1080 & 1<=n]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
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
( [(224::,0 ); (224::,0 )]) :sll_ms.ss:259: 13: bind: node  v_node_259_750'::node<val_259_751',next_259_752'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):sll_ms.ss:259: 13:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(224::,0 ); (224::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_259_750'=q_1103 & v_node_259_750'=null |-  v_node_259_750'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [n,DEL,x]
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::ref [x]
                                EXISTS(m: x'::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([0<=m & DEL(m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::ref [x]
                              EXISTS(m_1162: x'::sll<m_1162>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m_1162 & 0<=n & DEL(m_1162,n)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int result FAIL-1

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
                              EXISTS(m_1258: res::sll<m_1258>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([m_1258<=n & 0<=n & (-1+n)<=m_1258 & 0<=m_1258]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=m & 1<=m) --> DEL2(m,n),
 (-1+n=m & 0<=m) --> DEL2(m,n),
 (0<=n_1210 & 1+m_1224=m & -1+n=n_1210 & DEL2(m_1224,n_1210) & 
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
                              or EXISTS(Anon_1355,
                                 m_1356: res::node<m_1356,Anon_1355>@M[Orig][]&
                                 (([v<=m_1356][res!=null][0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (v<=m) --> FGE(v,m),
 (exists(Anon_1318:m=m_1353 & (1+Anon_1318)<=v & FGE(v,m_1353))) --> FGE(v,m)]
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
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              x::node<Anon_1371,q_1372>@M[Orig][]&(
                              ([x!=null][1<=m & 0<=m][res=Anon_1371]))&
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
                                EXISTS(flted_146_95,v,
                                m: x'::node<v,flted_146_95>@M[Orig][] * 
                                res::sll<m>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_146_95][0<=m & GN(m,n)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n][x!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              EXISTS(flted_146_1400,v_1401,
                              m_1402: x'::node<v_1401,flted_146_1400>@M[Orig][] * 
                              res::sll<m_1402>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=m_1402 & 0<=n & -1+n=m_1402 & 1<=n]
                               [x'!=null][null=flted_146_1400]))&
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
                              EXISTS(m_1444: res::sll<m_1444>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m_1444 & 0<=n & -2+n=m_1444 & 2<=n]))&
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
                              EXISTS(m_1465: res::sll<m_1465>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=m_1465 & 0<=n & -1+n=m_1465 & 1<=n]))&
                              {FLOW,(20,21)=__norm}))
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
                              EXISTS(m_1561: res::sll<m_1561>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=m_1561 & 0<=n & -1+m_1561=n & 1<=m_1561]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=1 & n=0) --> INS(m,n),
 (1+n=m & 2<=m) --> INS(m,n),
 (0<=n_1502 & 1+m_1516=m & -1+n=n_1502 & INS(m_1516,n_1502) & 
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
                              EXISTS(m_1669: res::sll<m_1669>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=m_1669 & 0<=n & -1+m_1669=n & 1<=m_1669]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=1 & n=0) --> INS2(m,n),
 (1+n=m & 2<=m) --> INS2(m,n),
 (0<=n_1610 & 1+m_1626=m & -1+n=n_1610 & INS2(m_1626,n_1610) & 
  1<=m) --> INS2(m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(m,n)
!!! POST:  n>=0 & n=m
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
                              EXISTS(n_1741,
                              m_1742: x::sll<n_1741>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              res::sll<m_1742>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([n=n_1741 & n=m_1742 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (0<=n_1692 & 1+m_1705=m & -1+n=n_1692 & 1<=m & 
  CPY(m_1705,n_1692)) --> CPY(m,n),
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
                              EXISTS(m_1819: res::sll<m_1819>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([n=m_1819 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (FIL(m_1801,n_1787) & 1<=m & -1+n=n_1787 & 1+m_1801=m & 
  0<=n_1787) --> FIL(m,n),
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
                              EXISTS(m_1867: x::sll<m_1867>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([n=m_1867 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=0) --> TRAV(m,n),
 (0<=n_1843 & 1+m_1850=m & -1+n=n_1843 & TRAV(m_1850,n_1843) & 
  1<=m) --> TRAV(m,n),
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
                    EBase true&(([MayLoop][0<=n1][0<=n2]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 21::
                              EXISTS(m_1950: res::sll<m_1950>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=m_1950 & m_1950=n1+n2 & 0<=n2 & 0<=n1 & 
                                 n1<=m_1950]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=m & n2=0 & 0<=m) --> MRG(m,n1,n2),
 (n2=m & n1=0 & 1<=m) --> MRG(m,n1,n2),
 (2<=n1_1923 & 1<=n2_1924 & m_1943=m & -1+n2=n2_1924 & 1+n1=n1_1923 & 0<=m & 
  MRG(m_1943,n1_1923,n2_1924)) --> MRG(m,n1,n2),
 (n2=1 & 1+n1=m & 2<=m) --> MRG(m,n1,n2)]
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
                              EXISTS(n_1977: x'::sll<n_1977>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([0<=n_1977 & 0<=m & -1+m=n_1977 & 1<=m]))&
                              {FLOW,(20,21)=__norm}))
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
                              EXISTS(m_1991: x'::sll<m_1991>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=m_1991 & 0<=n & -1+m_1991=n & 1<=m_1991]))&
                              {FLOW,(20,21)=__norm}))
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
                              EXISTS(k_2027: x'::sll<k_2027>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=k_2027 & 0<=j & -1+k_2027=j & 1<=k_2027]
                               [0<=i]))&
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
              EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [x]
                                EXISTS(flted_191_90,
                                v: x'::node<v,flted_191_90>@M[Orig][]&(
                                ([null=flted_191_90][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [x]
                              x'::node<v,flted_191_90>@M[Orig][]&(
                              ([x'=x & x'!=null][1<=n & 0<=n]
                               [null=flted_191_90]))&
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
                                EXISTS(flted_169_92,
                                v: x'::node<v,flted_169_92>@M[Orig][]&(
                                ([null=flted_169_92][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::sll<n>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              x'::node<v,flted_169_92>@M[Orig][]&(
                              ([x'=x & x'!=null][1<=n & 0<=n]
                               [null=flted_169_92]))&
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
 (0<=m_2104 & res=v_int_54_951' & -1+m=m_2104 & SIZEH(v_int_54_951',m_2104,n-
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
                              EXISTS(n1_2225,
                              n2_2226: x'::sll<n1_2225>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              res::sll<n2_2226>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=n2_2226 & 0<=n & n=n1_2225+n2_2226 & 
                                 1<=n1_2225 & 0<=n1_2225 & (1+n1_2225)<=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=1 & -1+n=n2 & 1<=n2) --> SPLIT(n,n1,n2),
 (exists(a:n2_2208=n2 & 1+n1_2207=n1 & -1+n=n_2176 & 
  SPLIT(n_2176,n1_2207,n2_2208) & 0<=n2 & 1<=n1 & 2<=a & 
  a<=n_2176)) --> SPLIT(n,n1,n2)]
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
                              EXISTS(m1_2234,
                              n1_2235: x'::sll<n1_2235>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              y'::sll<m1_2234>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([m=n1_2235 & 0<=m][n=m1_2234 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=n1 & n=m1 & 0<=n1 & 0<=m1) --> SWAP(m,n,m1,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1228 invocations 
20 false contexts at: ( (174,13)  (174,4)  (358,10)  (358,6)  (357,10)  (357,6)  (37,4)  (37,11)  (39,4)  (39,11)  (305,4)  (305,11)  (310,4)  (310,11)  (309,10)  (309,4)  (308,9)  (308,13)  (308,4)  (308,4) )

Total verification time: 1.97 second(s)
	Time spent in main process: 1.42 second(s)
	Time spent in child processes: 0.55 second(s)
