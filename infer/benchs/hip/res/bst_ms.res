
Processing file "bst_ms.ss"
Parsing bst_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  APP(k,m,n)
!!! POST:  m>=0 & k>=m & k=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[Anon_13; m; Anon_14; 
                    n](ex)x::dll<Anon_13,m>@M[Orig][LHSCase]@ rem br[{284,283}] * 
                    y::dll<Anon_14,n>@M[Orig][LHSCase]@ rem br[{284,283}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(r,
                                k: res::dll<r,k>@M[Orig][LHSCase]@ rem br[{284,283}]&
                                (([0<=k & APP(k,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_13; m; Anon_14; 
                  n](ex)x::dll<Anon_13,m>@M[Orig][LHSCase]@ rem br[{284,283}] * 
                  y::dll<Anon_14,n>@M[Orig][LHSCase]@ rem br[{284,283}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(r_968,
                              k_969: res::dll<r_968,k_969>@M[Orig][LHSCase]@ rem br[{284,283}]&
                              (
                              ([0<=k_969 & k_969=m+n & 0<=n & 0<=m & m<=k_969]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & k=n & 0<=n) --> APP(k,m,n),
 (m_845=m-1 & k=k_870+1 & n=n_847 & 1<=m & 1<=k_870 & 0<=n_847 & 
  APP(k_870,m_845,n_847)) --> APP(k,m,n),
 (k_870=0 & k=1 & m_845=m-1 & n=n_847 & 1<=m & 0<=n_847 & 
  APP(k_870,m_845,n_847)) --> APP(k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure appendC$node2~node2... 
!!! REL :  C(k,m,n)
!!! POST:  m>=0 & k>=m & k=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{284,283}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{284,283}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::
                                EXISTS(Anon_15,
                                k: res::dll<Anon_15,k>@M[Orig][LHSCase]@ rem br[{284,283}]&
                                (([0<=k & C(k,m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{284,283}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{284,283}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::
                              EXISTS(Anon_1132,
                              k_1133: res::dll<Anon_1132,k_1133>@M[Orig][LHSCase]@ rem br[{284,283}]&
                              (
                              ([0<=k_1133 & k_1133=m+n & 0<=n & 0<=m & 
                                 m<=k_1133]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & k=n & 0<=n) --> C(k,m,n),
 (m_1009=m-1 & k=k_1036+1 & n=n_1011 & 1<=m & 1<=k_1036 & 0<=n_1011 & 
  C(k_1036,m_1009,n_1011)) --> C(k,m,n),
 (k_1032=0 & m_1009=m-1 & k=1 & n=n_1011 & 1<=m & 0<=n_1011 & 
  C(k_1032,m_1009,n_1011)) --> C(k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appendC$node2~node2 SUCCESS

Checking procedure count$node2... 
!!! REL :  CNT(res,n,n1)
!!! POST:  n>=0 & n=res & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CNT]
              EBase exists (Expl)(Impl)[n](ex)z::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(n1: z::bst0<n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=n1 & CNT(res,n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)z::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(n1_1219: z::bst0<n1_1219>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([n=res & n=n1_1219 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & n1=0 & n=0) --> CNT(res,n,n1),
 (n=0 & n1=0 & res=0) --> CNT(res,n,n1),
 (cleft_83'=(res-cright_84')-1 & n_1165=(n-n_1180)-1 & n1=n1_1177+n1_1195+
  1 & 0<=n_1180 & n_1180<n & 0<=n1_1177 & 0<=n1_1195 & 
  CNT(cleft_83',n_1165,n1_1177) & 
  CNT(cright_84',n_1180,n1_1195)) --> CNT(res,n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure delete$node2~int... 
!!! REL :  DEL(n,n1)
!!! POST:  (n+1)>=n1 & n1>=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n1](ex)x::bst0<n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=n1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::ref [x]
                                EXISTS(n: x'::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=n & DEL(n,n1)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1](ex)x::bst0<n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=n1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::ref [x]
                              EXISTS(n_1408: x'::bst0<n_1408>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([0<=n_1408 & 0<=n1 & n_1408<=n1 & (-1+
                                 n1)<=n_1408]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=n1-1 & 2<=n1) --> DEL(n,n1),
 (false) --> DEL(n,n1),
 (n1=n+1 & 1<=n) --> DEL(n,n1),
 (n=(n_1376+n1)-n1_1275 & 0<=n1_1275 & n1_1275<n1 & 0<=n_1376 & 
  DEL(n_1376,n1_1275)) --> DEL(n,n1),
 (n=(n_1392+n1)-n1_1284 & 0<=n1_1284 & n1_1284<n1 & 0<=n_1392 & 
  DEL(n_1392,n1_1284)) --> DEL(n,n1),
 (n=0 & n1=0) --> DEL(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                EXISTS(q,
                                m1: x::dll<q,m1>@M[Orig][LHSCase]@ rem br[{284,283}]&
                                (([0<=m1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 21::
                              
                              EXISTS(m1_1609: true&(
                              ([0<=m1_1609][null=x][0=m & 0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(q_1610,
                                 m1_1611: x::dll<q_1610,m1_1611>@M[Orig][LHSCase]@ rem br[{284,283}]&
                                 (
                                 ([1<=m & 0<=m][x!=null][2<=m1_1611]
                                  [null=q_1610]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(q_1612,
                                 m1_1613: x::dll<q_1612,m1_1613>@M[Orig][LHSCase]@ rem br[{284,283}]&
                                 (
                                 ([1<=m & 0<=m][x!=null][null=q_1612]
                                  [1=m1_1613]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure flatten$node2 SUCCESS

Checking procedure insert$node2~int... 
!!! REL :  INS(m,m1)
!!! POST:  m>=0 & m+1=m1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(m1: res::bst0<m1>@M[Orig][LHSCase]@ rem br[{285}]&
                                (([null!=res][0!=m1 & 0<=m1 & INS(m,m1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(m1_1743: res::bst0<m1_1743>@M[Orig][LHSCase]@ rem br[{285}]&
                              (
                              ([0!=m1_1743 & 1+m=m1_1743 & 0<=m & 0<=m1_1743]
                               [null!=res]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & m1=1) --> INS(m,m1),
 (m1=(m1_1674+m)-m_1660 & 0<=m_1660 & m_1660<m & 1<=m1_1674 & 
  INS(m_1660,m1_1674)) --> INS(m,m1),
 (m1=(m1_1694+m)-m_1680 & 0<=m_1680 & m_1680<m & 1<=m1_1694 & 
  INS(m_1680,m1_1694)) --> INS(m,m1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Checking procedure remove_min$node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  RMV_MIN(n,n1)
!!! POST:  n1>=0 & n1+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV_MIN,x]
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::ref [x]
                                EXISTS(n1: x'::bst0<n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=n1 & RMV_MIN(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 34::ref [x]
                              EXISTS(n1_1815: x'::bst0<n1_1815>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([1+n1_1815=n & 0<=n & 0<=n1_1815]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=n-1 & 1<=n) --> RMV_MIN(n,n1),
 (n=(n_1785-n1_1801)+n1 & 0<=n1_1801 & n1_1801<n1 & 1<=n_1785 & 
  RMV_MIN(n_1785,n1_1801)) --> RMV_MIN(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Checking procedure search$node2~int... 
!!! REL :  SEA(n,n1)
!!! POST:  n>=0 & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SEA]
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(n1: x::bst0<n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([res | !(res)][0<=n1 & SEA(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(n1_1937: x::bst0<n1_1937>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([n=n1_1937 & 0<=n][res | !(res)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=0) --> SEA(n,n1),
 (n1=n & 1<=n) --> SEA(n,n1),
 (n_1857=(n+n1_1903)-n1 & 0<=n1_1903 & n1_1903<n1 & n1<=(n+n1_1903) & 
  SEA(n_1857,n1_1903)) --> SEA(n,n1),
 (n_1867=(n-n1)+n1_1919 & 0<=n1_1919 & n1_1919<n1 & n1<=(n+n1_1919) & 
  SEA(n_1867,n1_1919)) --> SEA(n,n1),
 (n=0 & n1=0) --> SEA(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
!!! REL :  TRAV(n,n1)
!!! POST:  n1>=0 & n1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(n1: x::bst0<n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=n1 & TRAV(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(n1_1999: x::bst0<n1_1999>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([n=n1_1999 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=0) --> TRAV(n,n1),
 (n_1972=(n-n_1966)-1 & n1=n1_1976+n1_1981+1 & 0<=n_1966 & n_1966<n & 
  0<=n1_1976 & 0<=n1_1981 & TRAV(n_1972,n1_1981) & 
  TRAV(n_1966,n1_1976)) --> TRAV(n,n1),
 (n=0 & n1=0) --> TRAV(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 1281 invocations 
0 false contexts at: ()

Total verification time: 0.82 second(s)
	Time spent in main process: 0.33 second(s)
	Time spent in child processes: 0.49 second(s)
