
Processing file "bst_msh.ss"
Parsing bst_msh.ss ...
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
                              EXISTS(n_1312,
                              h1_1313: z::bst1<n_1312,h1_1313>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([h=h1_1313 & 0<=h][res=n & res=n_1312 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> CNT(h,h1),
 (h=0 & h1=0) --> CNT(h,h1),
 ((h1=h1_1260+1 & h=h_1246+1 & 0<=h_1264 & h_1264<=h_1246 & 0<=h1_1281 & 
  h1_1281<=h1_1260 | h1=h1_1281+1 & h=h_1264+1 & 0<=h1_1260 & 
  h1_1260<h1_1281 & 0<=h_1246 & h_1246<h_1264 | h1=h1_1281+1 & h=h_1246+1 & 
  0<=h_1264 & h_1264<=h_1246 & 0<=h1_1260 & h1_1260<h1_1281 | h1=h1_1260+1 & 
  h=h_1264+1 & 0<=h1_1281 & h1_1281<=h1_1260 & 0<=h_1246 & h_1246<h_1264) & 
  CNT(h_1264,h1_1281) & CNT(h_1246,h1_1260)) --> CNT(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure count$node2 SUCCESS

Checking procedure delete$node2~int... 
!!! REL :  DEL(n,n1)
!!! POST:  (n+1)>=n1 & n1>=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[sn; 
                    n1](ex)x::bst1<sn,n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                    (([0<=sn][0<=n1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::ref [x]
                                EXISTS(sn1,
                                n: x'::bst1<sn1,n>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (([0<=n & DEL(n,n1)][0<=sn1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sn; 
                  n1](ex)x::bst1<sn,n1>@M[Orig][LHSCase]@ rem br[{286,285}]&(
                  ([0<=sn][0<=n1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::ref [x]
                              EXISTS(sn1_1573,
                              n_1574: x'::bst1<sn1_1573,n_1574>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([0<=n_1574 & 0<=n1 & n_1574<=n1 & (-1+
                                 n1)<=n_1574]
                               [0<=sn1_1573][0<=sn]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=n1-1 & 2<=n1) --> DEL(n,n1),
 (false) --> DEL(n,n1),
 (n1=n+1 & 1<=n) --> DEL(n,n1),
 ((n1=n & 0<=n1_1384 & n1_1384<n & 0<=n_1528 & n_1528<n | n=n_1528+1 & 
  n1=n1_1384+1 & 1<=n_1528 & 1<=n1_1384 | n=n_1528+1 & 0<=n1_1384 & 
  n1_1384<n1 & n1<=n_1528 | n1=n1_1384+1 & 0<=n_1528 & n_1528<n & 
  n<=n1_1384) & DEL(n_1528,n1_1384)) --> DEL(n,n1),
 ((n=n_1551+1 & n1_1396=n1-1 & 1<=n1 & 0<=n_1551 | n=n1 & 0<=n_1551 & 
  n_1551<=(n1-2) & 0<=n1_1396 & n1_1396<=(n1-2) | n1_1396=n1-1 & 0<=n_1551 & 
  n_1551<=(n-2) & n<=n1 | n=n_1551+1 & (n1_1396+2)<=n1 & n1<=(n_1551+1) & 
  0<=n1_1396) & DEL(n_1551,n1_1396)) --> DEL(n,n1),
 (n=0 & n1=0) --> DEL(n,n1)]
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
                              EXISTS(flted_118_1952,
                              n_1953: res::bst1<flted_118_1952,n_1953>@M[Orig][LHSCase]@ rem br[{285}]&
                              (
                              ([0!=n_1953 & 0<=n1 & n1<=n_1953 & (-1+
                                 n_1953)<=n1 & 0<=n_1953]
                               [null!=res]
                               [0!=flted_118_1952 & 0<=m & -1+
                                 flted_118_1952=m & 0<=flted_118_1952]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=1) --> INS(n,n1),
 ((n=n_1861+1 & n1_1841=n1-1 & 1<=n1 & 1<=n_1861 | n=n1 & 1<=n_1861 & 
  n_1861<=(n1-2) & 0<=n1_1841 & n1_1841<=(n1-2) | n1_1841=n1-1 & 1<=n_1861 & 
  n_1861<=(n-2) & n<=n1 | n=n_1861+1 & (n1_1841+2)<=n1 & n1<=(n_1861+1) & 
  0<=n1_1841) & INS(n_1861,n1_1841)) --> INS(n,n1),
 ((n1=n & 0<=n1_1868 & n1_1868<n & 1<=n_1888 & n_1888<n | n=n_1888+1 & 
  n1=n1_1868+1 & 1<=n_1888 & 1<=n1_1868 | n=n_1888+1 & 0<=n1_1868 & 
  n1_1868<n1 & n1<=n_1888 | n1=n1_1868+1 & 1<=n_1888 & n_1888<n & 
  n<=n1_1868) & INS(n_1888,n1_1868)) --> INS(n,n1)]
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
                                EXISTS(flted_152_75,
                                n1: x'::bst1<flted_152_75,n1>@M[Orig][LHSCase]@ rem br[{286,285}]&
                                (
                                ([0<=flted_152_75 & 1+flted_152_75=sn]
                                 [0<=n1 & RMV_MIN(n,n1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[sn; 
                  n](ex)x::bst1<sn,n>@M[Orig][LHSCase]@ rem br[{285}]&(
                  ([x!=null][1<=sn][1<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              EXISTS(flted_152_2047,
                              n1_2048: x'::bst1<flted_152_2047,n1_2048>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([0<=n1_2048 & 0<=n & n1_2048<=n & (-1+
                                 n)<=n1_2048]
                               [0<=flted_152_2047 & 0<=sn & 1+
                                 flted_152_2047=sn]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=n1+1 & 0<=n1) --> RMV_MIN(n,n1),
 ((n1=n1_2028+1 & n_2005=n-1 & 2<=n & 0<=n1_2028 | n1=n & 0<=n1_2028 & 
  n1_2028<=(n-2) & 1<=n_2005 & n_2005<=(n-2) | n_2005=n-1 & 0<=n1_2028 & 
  n1_2028<=(n1-2) & n1<=n | n1=n1_2028+1 & (n_2005+2)<=n & n<=(n1_2028+1) & 
  1<=n_2005) & RMV_MIN(n_2005,n1_2028)) --> RMV_MIN(n,n1)]
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
                              EXISTS(n_2202,
                              h1_2203: x::bst1<n_2202,h1_2203>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (
                              ([h=h1_2203 & 0<=h][n=n_2202 & 0<=n]
                               [res | !(res)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> SEA(h,h1),
 (h1=h & 1<=h) --> SEA(h,h1),
 ((h=h1 & 0<=h_2100 & h_2100<h1 & 0<=h1_2156 & h1_2156<h1 | h1=h1_2156+1 & 
  h=h_2100+1 & 1<=h_2100 & 1<=h1_2156 | h1=h1_2156+1 & 0<=h_2100 & 
  h_2100<h & h<=h1_2156 | h=h_2100+1 & 0<=h1_2156 & h1_2156<h1 & 
  h1<=h_2100) & SEA(h_2100,h1_2156)) --> SEA(h,h1),
 ((h1=h1_2177+1 & h_2113=h-1 & 1<=h & 0<=h1_2177 | h1=h & 0<=h1_2177 & 
  h1_2177<=(h-2) & 0<=h_2113 & h_2113<=(h-2) | h_2113=h-1 & 0<=h1_2177 & 
  h1_2177<=(h1-2) & h1<=h | h1=h1_2177+1 & (h_2113+2)<=h & h<=(h1_2177+1) & 
  0<=h_2113) & SEA(h_2113,h1_2177)) --> SEA(h,h1),
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
                              EXISTS(n_2287,
                              h1_2288: x::bst1<n_2287,h1_2288>@M[Orig][LHSCase]@ rem br[{286,285}]&
                              (([h=h1_2288 & 0<=h][n=n_2287 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (h1=0 & h=0) --> TRAV(h,h1),
 ((h1=h1_2255+1 & h=h_2242+1 & 0<=h_2251 & h_2251<=h_2242 & 0<=h1_2262 & 
  h1_2262<=h1_2255 | h1=h1_2262+1 & h=h_2251+1 & 0<=h1_2255 & 
  h1_2255<h1_2262 & 0<=h_2242 & h_2242<h_2251 | h1=h1_2262+1 & h=h_2242+1 & 
  0<=h_2251 & h_2251<=h_2242 & 0<=h1_2255 & h1_2255<h1_2262 | h1=h1_2255+1 & 
  h=h_2251+1 & 0<=h1_2262 & h1_2262<=h1_2255 & 0<=h_2242 & h_2242<h_2251) & 
  TRAV(h_2242,h1_2255) & TRAV(h_2251,h1_2262)) --> TRAV(h,h1),
 (h=0 & h1=0) --> TRAV(h,h1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure traverse$node2 SUCCESS

Termination checking result:

Stop Omega... 1588 invocations 
0 false contexts at: ()

Total verification time: 1.12 second(s)
	Time spent in main process: 0.42 second(s)
	Time spent in child processes: 0.7 second(s)
