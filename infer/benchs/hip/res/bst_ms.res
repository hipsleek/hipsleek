
Processing file "bst_ms.ss"
Parsing bst_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
!!! REL :  APP(k,m,n)
!!! POST:  m>=0 & n>=0 & m+n=k
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[Anon_13; m; Anon_14; 
                    n](ex)x::dll<Anon_13,m>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                    y::dll<Anon_14,n>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(r,
                                k: res::dll<r,k>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=k & APP(k,m,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_13; m; Anon_14; 
                  n](ex)x::dll<Anon_13,m>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                  y::dll<Anon_14,n>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(r_975,
                              k_976: res::dll<r_975,k_976>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([0<=k_976 & m+n=k_976 & 0<=m & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (0<=m_852 & k_877=0 & n_854=n & k=1 & -1+m=m_852 & 0<=n & 
  APP(k_877,m_852,n_854)) --> APP(k,m,n),
 (m=0 & n=k & 0<=k) --> APP(k,m,n),
 (0<=m_852 & n_854=n & -1+m=m_852 & 1+k_877=k & 2<=k & 
  APP(k_877,m_852,n_854) & 0<=n) --> APP(k,m,n),
 (0<=m_852 & k_877=0 & n_854=n & k=1 & -1+m=m_852 & 0<=n & 
  APP(k_877,m_852,n_854)) --> APP(k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node2~node2 SUCCESS

Checking procedure appendC$node2~node2... 
!!! REL :  C(k,m,n)
!!! POST:  m>=0 & k>=m & k=n+m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [C]
              EBase exists (Expl)(Impl)[q; m; p; 
                    n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                    y::dll<p,n>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::
                                EXISTS(Anon_15,
                                k: res::dll<Anon_15,k>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=k & C(k,m,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; p; 
                  n](ex)x::dll<q,m>@M[Orig][LHSCase]@ rem br[{286,285}] * 
                  y::dll<p,n>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::
                              EXISTS(Anon_1139,
                              k_1140: res::dll<Anon_1139,k_1140>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([0<=k_1140 & k_1140=m+n & 0<=n & 0<=m & 
                                 m<=k_1140]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & n=k & 0<=k) --> C(k,m,n),
 (0<=m_1016 & n_1018=n & -1+m=m_1016 & 1+k_1043=k & 2<=k & 0<=n & 
  C(k_1043,m_1016,n_1018)) --> C(k,m,n),
 (0<=m_1016 & k_1039=0 & n_1018=n & -1+m=m_1016 & k=1 & 0<=n & 
  C(k_1039,m_1016,n_1018)) --> C(k,m,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure appendC$node2~node2 SUCCESS

Checking procedure count$node2... 
!!! REL :  CNT(res,n,n1)
!!! POST:  n>=0 & n=res & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CNT]
              EBase exists (Expl)(Impl)[n](ex)z::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(n1: z::bst0<n1>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                (([0<=n1 & CNT(res,n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)z::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(n1_1226: z::bst0<n1_1226>@M[Orig][LHSCase]@ rem br[{288,287}]&
                              (([n=res & n=n1_1226 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res=0 & n1=0 & n=0) --> CNT(res,n,n1),
 (n=0 & n1=0 & res=0) --> CNT(res,n,n1),
 (0<=n_1172 & 0<=n_1187 & 1+cleft_83'+cright_84'=res & n=1+n_1172+n_1187 & 
  CNT(cleft_83',n_1172,n1_1184) & CNT(cright_84',n_1187,n1_1202) & 
  0<=n1_1184 & 1+n1_1184+n1_1202=n1 & (1+n1_1184)<=n1) --> CNT(res,n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure delete$node2~int... 
assert:bst_ms.ss:194: 16:  : ok


!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::ref [x]
                                EXISTS(n1: x'::bst0<n1>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                (([0<=n1 & n1<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::ref [x]
                              
                              EXISTS(f_1416,q_1417,
                              n1_1418: x'::node2<a,x',q_1417>@M[Orig][] * 
                              x'::bst0<n1_1418>@M[Orig][LHSCase]@ rem br[{288,287}]&
                              (
                              ([x'!=null][-1+n=n1_1418 & 0<=n & 1<=n1_1418]
                               [x!=null][null=q_1417]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_1419: x'::bst0<n1_1419>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                 (
                                 ([x'=x & x'!=null]
                                  [1<=n1_1419 & 0<=n & n1_1419<=n]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(n1_1420: true&(
                                 ([null=x][null=x'][0=n & 0<=n][0=n1_1420]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                EXISTS(q,
                                m1: x::dll<q,m1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=m1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 21::
                              
                              EXISTS(m1_1621: true&(
                              ([0<=m1_1621][null=x][0=m & 0<=m]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(q_1622,
                                 m1_1623: x::dll<q_1622,m1_1623>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                 (
                                 ([1<=m & 0<=m][x!=null][2<=m1_1623]
                                  [null=q_1622]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(q_1624,
                                 m1_1625: x::dll<q_1624,m1_1625>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                 (
                                 ([x!=null][1<=m & 0<=m][null=q_1624]
                                  [1=m1_1625]))&
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
              EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=m]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(m1: res::bst0<m1>@M[Orig][LHSCase]@ rem br[{287}]&
                                (([null!=res][0!=m1 & 0<=m1 & INS(m,m1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m](ex)x::bst0<m>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=m]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(m1_1755: res::bst0<m1_1755>@M[Orig][LHSCase]@ rem br[{287}]&
                              (
                              ([0!=m1_1755 & 1+m=m1_1755 & 0<=m & 0<=m1_1755]
                               [null!=res]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & m1=1) --> INS(m,m1),
 (0<=m_1672 & INS(m_1672,m1_1686) & 1<=m1_1686 & m+m1_1686=m1+m_1672 & (1+
  m1_1686)<=m1) --> INS(m,m1),
 (0<=m_1692 & INS(m_1692,m1_1706) & (1+m1_1706)<=m1 & m+m1_1706=m1+m_1692 & 
  m1<=(-1+m1+m1_1706)) --> INS(m,m1)]
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
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::ref [x]
                                EXISTS(n1: x'::bst0<n1>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                (([0<=n1 & RMV_MIN(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 34::ref [x]
                              EXISTS(n1_1827: x'::bst0<n1_1827>@M[Orig][LHSCase]@ rem br[{288,287}]&
                              (([1+n1_1827=n & 0<=n & 0<=n1_1827]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (-1+n=n1 & 0<=n1) --> RMV_MIN(n,n1),
 (RMV_MIN(n_1797,n1_1813) & 0<=n1_1813 & n1+n_1797=n+n1_1813 & (1+
  n1_1813)<=n1 & n1<=(-1+n+n1_1813)) --> RMV_MIN(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Checking procedure search$node2~int... 
!!! REL :  SEA(n,n1)
!!! POST:  n>=0 & n=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SEA]
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(n1: x::bst0<n1>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                (([res | !(res)][0<=n1 & SEA(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(n1_1949: x::bst0<n1_1949>@M[Orig][LHSCase]@ rem br[{288,287}]&
                              (([n=n1_1949 & 0<=n][res | !(res)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=0) --> SEA(n,n1),
 (exists(m1_1853:n=n1 & 0<=m1_1853 & (1+m1_1853)<=n1)) --> SEA(n,n1),
 (SEA(n_1869,n1_1915) & 0<=n_1869 & n<=(n1+n_1869) & n+n1_1915=n1+n_1869 & 
  (1+n_1869)<=n) --> SEA(n,n1),
 (SEA(n_1879,n1_1931) & 0<=n_1879 & (n1+n_1879)<=(-1+n+n1) & n+n1_1931=n1+
  n_1879 & n<=(n1+n_1879)) --> SEA(n,n1),
 (n=0 & n1=0) --> SEA(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
!!! REL :  TRAV(n,n1)
!!! POST:  n1>=0 & n1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(n1: x::bst0<n1>@M[Orig][LHSCase]@ rem br[{288,287}]&
                                (([0<=n1 & TRAV(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::bst0<n>@M[Orig][LHSCase]@ rem br[{288,287}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              EXISTS(n1_2011: x::bst0<n1_2011>@M[Orig][LHSCase]@ rem br[{288,287}]&
                              (([n=n1_2011 & 0<=n]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=0) --> TRAV(n,n1),
 (0<=n_1984 & 0<=n_1978 & n=1+n_1978+n_1984 & TRAV(n_1984,n1_1993) & 
  TRAV(n_1978,n1_1988) & 0<=n1_1988 & 1+n1_1988+n1_1993=n1 & (1+
  n1_1988)<=n1) --> TRAV(n,n1),
 (n=0 & n1=0) --> TRAV(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 1266 invocations 
0 false contexts at: ()

Total verification time: 0.74 second(s)
	Time spent in main process: 0.32 second(s)
	Time spent in child processes: 0.42 second(s)
