
Processing file "bst_msh.ss"
Parsing bst_msh.ss ...
WARNING : parsing problem RMV_MIN is neither a ranking function nor a relation
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node2~node2... 
Procedure append$node2~node2 SUCCESS

Checking procedure appendC$node2~node2... 
Procedure appendC$node2~node2 SUCCESS

Checking procedure count$node2... 
!!! REL :  CNT(h,h1)
!!! POST:  h1>=0 & h1=h
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CNT]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)z::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 15::
                                EXISTS(n_92,
                                h1: z::bst1<n_92,h1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (
                                ([0<=h1 & CNT(h,h1)]
                                 [n=n_92 & n=res & 0<=n_92]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)z::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 15::
                              EXISTS(n_1309,
                              h1_1310: z::bst1<n_1309,h1_1310>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([h=h1_1310 & 0<=h][res=n & res=n_1309 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> CNT(h,h1),
 (h=0 & h1=0) --> CNT(h,h1),
 ((h1=h1_1257+1 & h=h_1243+1 & 0<=h_1261 & h_1261<=h_1243 & 0<=h1_1278 & 
  h1_1278<=h1_1257 | h1=h1_1278+1 & h=h_1261+1 & 0<=h1_1257 & 
  h1_1257<h1_1278 & 0<=h_1243 & h_1243<h_1261 | h1=h1_1278+1 & h=h_1243+1 & 
  0<=h_1261 & h_1261<=h_1243 & 0<=h1_1257 & h1_1257<h1_1278 | h1=h1_1257+1 & 
  h=h_1261+1 & 0<=h1_1278 & h1_1278<=h1_1257 & 0<=h_1243 & h_1243<h_1261) & 
  CNT(h_1261,h1_1278) & CNT(h_1243,h1_1257)) --> CNT(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure delete$node2~int... 
!!! REL :  DEL(h,h1)
!!! POST:  h>=0 & h1>=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::ref [x]
                                EXISTS(n1,
                                h1: x'::bst1<n1,h1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=h1 & DEL(h,h1)][0<=n1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::ref [x]
                              EXISTS(n1_1570,
                              h1_1571: x'::bst1<n1_1570,h1_1571>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([0<=h1_1571][0<=h][0<=n1_1570][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=h-1 & 2<=h) --> DEL(h,h1),
 (false) --> DEL(h,h1),
 (1<=h1 & 2<=h) --> DEL(h,h1),
 ((h=h1 & 0<=h_1381 & h_1381<h1 & 0<=h1_1525 & h1_1525<h1 | h1=h1_1525+1 & 
  h=h_1381+1 & 1<=h1_1525 & 1<=h_1381 | h1=h1_1525+1 & 0<=h_1381 & 
  h_1381<h & h<=h1_1525 | h=h_1381+1 & 0<=h1_1525 & h1_1525<h1 & 
  h1<=h_1381) & DEL(h_1381,h1_1525)) --> DEL(h,h1),
 ((h1=h1_1548+1 & h_1393=h-1 & 1<=h & 0<=h1_1548 | h1=h & 0<=h1_1548 & 
  h1_1548<=(h-2) & 0<=h_1393 & h_1393<=(h-2) | h_1393=h-1 & 0<=h1_1548 & 
  h1_1548<=(h1-2) & h1<=h | h1=h1_1548+1 & (h_1393+2)<=h & h<=(h1_1548+1) & 
  0<=h_1393) & DEL(h_1393,h1_1548)) --> DEL(h,h1),
 (h1=0 & h=0) --> DEL(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node2~int SUCCESS

Checking procedure flatten$node2... 
Procedure flatten$node2 SUCCESS

Checking procedure insert$node2~int... 
!!! REL :  INS(n,n1)
!!! POST:  (n1+1)>=n & n>=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[m; 
                    n1](ex)x::bst1<m,n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=m][0<=n1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                EXISTS(flted_118_88,
                                n: res::bst1<flted_118_88,n>@M[Orig][LHSCase]@ rem br[{285}]&
                                (
                                ([0!=flted_118_88 & 0<=flted_118_88 & -1+
                                   flted_118_88=m]
                                 [null!=res][0!=n & 0<=n & INS(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  n1](ex)x::bst1<m,n1>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=m][0<=n1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              EXISTS(flted_118_1949,
                              n_1950: res::bst1<flted_118_1949,n_1950>@M[Orig][LHSCase]@ rem br[{285}]&
                              (
                              ([0!=n_1950 & 0<=n1 & n1<=n_1950 & (-1+
                                 n_1950)<=n1 & 0<=n_1950]
                               [null!=res]
                               [0!=flted_118_1949 & 0<=m & -1+
                                 flted_118_1949=m & 0<=flted_118_1949]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=1) --> INS(n,n1),
 ((n=n_1858+1 & n1_1838=n1-1 & 1<=n1 & 1<=n_1858 | n=n1 & 1<=n_1858 & 
  n_1858<=(n1-2) & 0<=n1_1838 & n1_1838<=(n1-2) | n1_1838=n1-1 & 1<=n_1858 & 
  n_1858<=(n-2) & n<=n1 | n=n_1858+1 & (n1_1838+2)<=n1 & n1<=(n_1858+1) & 
  0<=n1_1838) & INS(n_1858,n1_1838)) --> INS(n,n1),
 ((n1=n & 0<=n1_1865 & n1_1865<n & 1<=n_1885 & n_1885<n | n=n_1885+1 & 
  n1=n1_1865+1 & 1<=n_1885 & 1<=n1_1865 | n=n_1885+1 & 0<=n1_1865 & 
  n1_1865<n1 & n1<=n_1885 | n1=n1_1865+1 & 1<=n_1885 & n_1885<n & 
  n<=n1_1865) & INS(n_1885,n1_1865)) --> INS(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node2~int SUCCESS

Checking procedure remove_min$node2... 
!!! REL :  RMV_MIN(n,n1)
!!! POST:  (n1+1)>=n & n>=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV_MIN]
              EBase exists (Expl)(Impl)[sn; 
                    n](ex)x::bst1<sn,n>@M[Orig][LHSCase]@ rem br[{285}]&(
                    ([null!=x][0<=sn & 0!=sn][0<=n & 0!=n]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::ref [x]
                                EXISTS(flted_153_75,
                                n1: x'::bst1<flted_153_75,n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (
                                ([0<=flted_153_75 & 1+flted_153_75=sn]
                                 [0<=n1 & RMV_MIN(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sn; 
                  n](ex)x::bst1<sn,n>@M[Orig][LHSCase]@ rem br[{285}]&(
                  ([x!=null][1<=sn][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              EXISTS(flted_153_2044,
                              n1_2045: x'::bst1<flted_153_2044,n1_2045>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([0<=n1_2045 & 0<=n & n1_2045<=n & (-1+
                                 n)<=n1_2045]
                               [0<=flted_153_2044 & 0<=sn & 1+
                                 flted_153_2044=sn]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=n1+1 & 0<=n1) --> RMV_MIN(n,n1),
 ((n1=n1_2025+1 & n_2002=n-1 & 2<=n & 0<=n1_2025 | n1=n & 0<=n1_2025 & 
  n1_2025<=(n-2) & 1<=n_2002 & n_2002<=(n-2) | n_2002=n-1 & 0<=n1_2025 & 
  n1_2025<=(n1-2) & n1<=n | n1=n1_2025+1 & (n_2002+2)<=n & n<=(n1_2025+1) & 
  1<=n_2002) & RMV_MIN(n_2002,n1_2025)) --> RMV_MIN(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node2 SUCCESS

Checking procedure search$node2~int... 
!!! REL :  SEA(h,h1)
!!! POST:  h>=0 & h=h1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SEA]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(n_64,
                                h1: x::bst1<n_64,h1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (
                                ([res | !(res)][0<=h1 & SEA(h,h1)]
                                 [n=n_64 & 0<=n_64]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(n_2199,
                              h1_2200: x::bst1<n_2199,h1_2200>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([h=h1_2200 & 0<=h][n=n_2199 & 0<=n]
                               [res | !(res)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> SEA(h,h1),
 (h1=h & 1<=h) --> SEA(h,h1),
 ((h=h1 & 0<=h_2097 & h_2097<h1 & 0<=h1_2153 & h1_2153<h1 | h1=h1_2153+1 & 
  h=h_2097+1 & 1<=h_2097 & 1<=h1_2153 | h1=h1_2153+1 & 0<=h_2097 & 
  h_2097<h & h<=h1_2153 | h=h_2097+1 & 0<=h1_2153 & h1_2153<h1 & 
  h1<=h_2097) & SEA(h_2097,h1_2153)) --> SEA(h,h1),
 ((h1=h1_2174+1 & h_2110=h-1 & 1<=h & 0<=h1_2174 | h1=h & 0<=h1_2174 & 
  h1_2174<=(h-2) & 0<=h_2110 & h_2110<=(h-2) | h_2110=h-1 & 0<=h1_2174 & 
  h1_2174<=(h1-2) & h1<=h | h1=h1_2174+1 & (h_2110+2)<=h & h<=(h1_2174+1) & 
  0<=h_2110) & SEA(h_2110,h1_2174)) --> SEA(h,h1),
 (h=0 & h1=0) --> SEA(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure search$node2~int SUCCESS

Checking procedure traverse$node2... 
!!! REL :  TRAV(h,h1)
!!! POST:  h1>=0 & h1=h
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                    ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(n_69,
                                h1: x::bst1<n_69,h1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=h1 & TRAV(h,h1)][n=n_69 & 0<=n_69]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  h](ex)x::bst1<n,h>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=n][0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(n_2284,
                              h1_2285: x::bst1<n_2284,h1_2285>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([h=h1_2285 & 0<=h][n=n_2284 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> TRAV(h,h1),
 ((h1=h1_2252+1 & h=h_2239+1 & 0<=h_2248 & h_2248<=h_2239 & 0<=h1_2259 & 
  h1_2259<=h1_2252 | h1=h1_2259+1 & h=h_2248+1 & 0<=h1_2252 & 
  h1_2252<h1_2259 & 0<=h_2239 & h_2239<h_2248 | h1=h1_2259+1 & h=h_2239+1 & 
  0<=h_2248 & h_2248<=h_2239 & 0<=h1_2252 & h1_2252<h1_2259 | h1=h1_2252+1 & 
  h=h_2248+1 & 0<=h1_2259 & h1_2259<=h1_2252 & 0<=h_2239 & h_2239<h_2248) & 
  TRAV(h_2239,h1_2252) & TRAV(h_2248,h1_2259)) --> TRAV(h,h1),
 (h=0 & h1=0) --> TRAV(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 1578 invocations 
0 false contexts at: ()

Total verification time: 1.12 second(s)
	Time spent in main process: 0.43 second(s)
	Time spent in child processes: 0.69 second(s)
