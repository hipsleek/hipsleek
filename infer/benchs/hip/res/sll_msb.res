/usr/local/bin/mona

Processing file "sll_msb.ss"
Parsing sll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure create_list$int~int... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
Context of Verification Failure: File "sll_msb.ss",Line:238,Col:10
Last Proving Location: File "sll_msb.ss",Line:244,Col:4

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([1<=a & (1+a)<=n][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(m,
                                S1: x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([DEL(S,S1)][true]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][null!=x][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              EXISTS(m_1569,
                              S1_1570: x::sll1<m_1569,S1_1570>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([DEL(S,S1_1570)][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_1414:exists(S1_1417:exists(S1_1384:exists(v_1381:exists(S1_1496:exists(v_1493:S1_1384!=() & 
  S1_1384=union(S1_1417,{v_1414}) & S1_1496=S1_1417 & v_1381=v_1493 & 
  S=union(S1_1384,{v_1381}) & S1=union(S1_1496,{v_1493}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1449:exists(m_1450:exists(n_1463:exists(a:exists(m_1526:exists(m_1521:exists(v_int_244_1523:exists(n:exists(v_bool_240_832':exists(x:exists(r_1525:exists(m:exists(S1_1527:exists(v_1524:exists(S1_1451:exists(v_1448:S1_1451!=() & 
  S1_1522!=() & (r_1449=r_1525 & S1_1522=S1_1527 & S1_1451=S_1464 & 
  v_1524=v_1448 & 1+m_1450=n & 1+n_1463=n & -1+a=v_int_244_1523 & m=0 & 
  m_1526=-1 & m_1521=-1 & 1<=v_int_244_1523 & (2+v_int_244_1523)<=n & 
  !(v_bool_240_832') & x!=null & r_1525!=null & DEL(S_1464,S1_1522) | 
  r_1449=r_1525 & S1_1522=S1_1527 & S1_1451=S_1464 & v_1524=v_1448 & 1+
  m_1450=n & 1+n_1463=n & -1+a=v_int_244_1523 & 1+m_1526=m & 1+m_1521=m & 
  1<=v_int_244_1523 & (2+v_int_244_1523)<=n & !(v_bool_240_832') & x!=null & 
  r_1525!=null & DEL(S_1464,S1_1522) & 2<=m) & S!=() & S1=union(S1_1527,
  {v_1524}) & S=union(S1_1451,{v_1448})))))))))))))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Context of Verification Failure: File "sll_msb.ss",Line:253,Col:10
Last Proving Location: File "sll_msb.ss",Line:266,Col:12

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(m,a,
                                S1: res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([m<=n & (-1+n)<=m][DEL2(a,S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              EXISTS(m_1774,a_1775,
                              S1_1776: res::sll1<m_1774,S1_1776>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([DEL2(a_1775,S,S1_1776)]
                               [m_1774<=n & 0<=n & (-1+n)<=m_1774]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v:exists(S1_1685:exists(v_1682:exists(S1_1597:exists(v_1594:(1+
  v)<=v_1682 & v_1594=v_1682 & S1_1685=S1_1597 & S1=union(S1_1685,
  {v_1682}) & S!=() & S=union(S1_1597,{v_1594}))))))) --> DEL2(a_1681,S,S1),
 (exists(v:exists(n:exists(r_1595:exists(res:exists(v_node_262_797':exists(m:exists(v_bool_258_805':exists(x:exists(v_bool_257_807':exists(v_bool_261_804':exists(m_1596:exists(S1_1597:exists(v_1594:(S1_1597=S1 & 
  v_1594=v & -1+n=m_1596 & r_1595=v_node_262_797' & res=v_node_262_797' & 
  m=m_1596 & v_bool_258_805'<=0 & m_1596<=-2 & x!=null & 
  1<=v_bool_257_807' & 1<=v_bool_261_804' | S1_1597=S1 & v_1594=v & -1+
  n=m_1596 & r_1595=v_node_262_797' & res=v_node_262_797' & m=m_1596 & 
  v_bool_258_805'<=0 & x!=null & 1<=v_bool_257_807' & 1<=v_bool_261_804' & 
  0<=m_1596) & S=union(S1_1597,{v_1594}) & 
  S!=())))))))))))))) --> DEL2(a_1707,S,S1),
 (exists(v:exists(S1_1724:exists(v_1721:exists(S1_1597:exists(v_1594:(1+
  v_1721)<=v & v_1594=v_1721 & S1_1597=S_1634 & S1_1670=S1_1724 & 
  DEL2(a_1669,S_1634,S1_1670) & S1=union(S1_1724,{v_1721}) & S!=() & 
  S=union(S1_1597,{v_1594}))))))) --> DEL2(a_1720,S,S1),
 (S1= & S=) --> DEL2(a_1752,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 81::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_18,
                                   m: res::node<m,Anon_18>@M[Orig][]&(
                                   ([FGE(S,m) & v<=m][res!=null]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 81::
                              
                              true&(([res=null][0<=n]))&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_18>@M[Orig][]&(
                                 ([res!=null][v<=m][0<=n]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(res:exists(Anon_18:exists(r_1853:exists(v_node_362_695':exists(m_1854:exists(v:exists(v_bool_358_701':exists(x:exists(v_bool_361_700':exists(n:exists(S1_1855:exists(v_1852:(res=x & 
  Anon_18=r_1853 & m=v_1852 & v_node_362_695'=x & 1+m_1854=n & n<=-1 & 
  v<=v_1852 & v_bool_358_701'<=0 & x!=null & 1<=v_bool_361_700' | res=x & 
  Anon_18=r_1853 & m=v_1852 & v_node_362_695'=x & 1+m_1854=n & v<=v_1852 & 
  v_bool_358_701'<=0 & x!=null & 1<=v_bool_361_700' & 1<=n) & S!=() & 
  S=union(S1_1855,{v_1852})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_1855:exists(v_1852:(1+v_1852)<=v & S1_1855=S_1880 & 
  m_1909=m & v<=m & FGE(S_1880,m_1909) & S=union(S1_1855,{v_1852}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S2,v)
!!! POST:  S2<subset> S  & v <in> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::ref [x]
                                EXISTS(flted_132_109,flted_132_110,S2,
                                v: x'::node<v,flted_132_110>@M[Orig][] * 
                                res::sll1<flted_132_109,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_132_110][1+flted_132_109=n]
                                 [GN(S,S2,v)][x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              x'::node<v,flted_132_110>@M[Orig][] * 
                              res::sll1<flted_132_109,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([S2<subset> S  & v <in> S ][x'!=null]
                               [1+flted_132_109=n & 0<=n][flted_132_110=null]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(tmp_111':exists(res:exists(r_1951:exists(v_node_136_990':exists(n:exists(flted_132_110:exists(x:exists(flted_132_109:exists(next_135_989':exists(x':exists(m_1952:exists(S1_1953:exists(v_1950:(tmp_111'=v_node_136_990' & 
  res=v_node_136_990' & r_1951=v_node_136_990' & v=v_1950 & S1_1953=S2 & -1+
  n=m_1952 & flted_132_110=next_135_989' & x=x' & flted_132_109=m_1952 & 
  m_1952<=-2 & next_135_989'=null & x'!=null | tmp_111'=v_node_136_990' & 
  res=v_node_136_990' & r_1951=v_node_136_990' & v=v_1950 & S1_1953=S2 & -1+
  n=m_1952 & flted_132_110=next_135_989' & x=x' & flted_132_109=m_1952 & 
  next_135_989'=null & x'!=null & 0<=m_1952) & S=union(S1_1953,{v_1950}) & 
  S!=())))))))))))))) --> GN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
( ) :sll_msb.ss:187: 9: bind: node  v_node_187_906'::node<val_187_907',next_187_908'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):sll_msb.ss:187: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_187_906'=r_2005 & v_node_187_906'=null |-  v_node_187_906'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_185_99,
                                S2: res::sll1<flted_185_99,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([2+flted_185_99=n][GNN(S,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              res::sll1<flted_185_99,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([2+flted_185_99=n & 0<=n][GNN(S,S2)]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node result FAIL-1

Checking procedure get_tail$node... 
!!! REL :  GT(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=n][S!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_167_103,
                                S1: res::sll1<flted_167_103,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([1+flted_167_103=n][GT(S,S1)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][(n+1)<=0 & x!=null | x!=null & 1<=n]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              res::sll1<flted_167_103,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([1+flted_167_103=n & 0<=n][S1<subset> S ]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(r_2062:exists(res:exists(v_node_169_934':exists(n:exists(flted_167_103:exists(x:exists(m_2063:exists(S1_2064:exists(v_2061:(r_2062=v_node_169_934' & 
  res=v_node_169_934' & S1_2064=S1 & -1+n=m_2063 & flted_167_103=m_2063 & 
  m_2063<=-2 & x!=null | r_2062=v_node_169_934' & res=v_node_169_934' & 
  S1_2064=S1 & -1+n=m_2063 & flted_167_103=m_2063 & x!=null & 0<=m_2063) & 
  S!=() & S=union(S1_2064,{v_2061}))))))))))) --> GT(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Context of Verification Failure: File "sll_msb.ss",Line:195,Col:10
Last Proving Location: File "sll_msb.ss",Line:208,Col:3

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(flted_195_96,S1,
                                a: res::sll1<flted_195_96,S1>@M[Orig][LHSCase]@ rem br[{383}]&
                                (
                                ([-1+flted_195_96=n][S1!=() & INS(S,S1,a)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              EXISTS(flted_195_2266,S1_2267,
                              a_2268: res::sll1<flted_195_2266,S1_2267>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([null!=res]
                               [S1_2267!=() & INS(S,S1_2267,a_2268)]
                               [-1+flted_195_2266=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v:exists(S1_2181:exists(v_2178:S1_2181= & v_2178=v & S= & 
  S1=union(S1_2181,{v_2178}))))) --> INS(S,S1,a_2177),
 (exists(v_2196:exists(v:exists(S1_2199:exists(S1_2192:exists(v_2189:exists(S1_2116:exists(v_2113:S1_2192=union(S1_2199,
  {v_2196}) & v_2189<=v_2196 & v_2113=v_2196 & v=v_2189 & S1_2116=S1_2199 & 
  S1=union(S1_2192,{v_2189}) & S=union(S1_2116,{v_2113}) & 
  S!=())))))))) --> INS(S,S1,a_2188),
 (exists(v:exists(S1_2116:exists(v_2113:exists(S1_2232:exists(v_2229:S1_2170!=() & 
  (1+v_2229)<=v & v_2113=v_2229 & S1_2116=S_2141 & S1_2170=S1_2232 & 
  INS(S_2141,S1_2170,a_2171) & S=union(S1_2116,{v_2113}) & S1=union(S1_2232,
  {v_2229}) & S!=())))))) --> INS(S,S1,a_2228)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Context of Verification Failure: File "sll_msb.ss",Line:217,Col:10
Last Proving Location: File "sll_msb.ss",Line:228,Col:2

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [INS2]
              EBase exists (Expl)(Impl)[n; S; v; 
                    Anon_17](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    vn::node<v,Anon_17>@M[Orig][]&(([true][vn!=null]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 44::
                                EXISTS(flted_217_94,S2,S1,
                                a: res::sll1<flted_217_94,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                                (
                                ([-1+flted_217_94=n][INS2(S,S1,a)][null!=res]
                                 [S2!=()]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S; v; 
                  Anon_17](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  vn::node<v,Anon_17>@M[Orig][]&(([vn!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 44::
                              EXISTS(flted_217_2471,S2_2472,S1_2473,
                              a_2474: res::sll1<flted_217_2471,S2_2472>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([S2_2472!=()][null!=res]
                               [INS2(S,S1_2473,a_2474)]
                               [-1+flted_217_2471=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S=) --> INS2(S,S1_2377,a_2378),
 (exists(v:exists(S2:exists(S1_2394:exists(v_2391:exists(v_2398:exists(S1_2401:exists(S1_2308:exists(v_2305:v=v_2391 & 
  S1_2394=union(S1_2401,{v_2398}) & S2=union(S1_2394,{v_2391}) & 
  v_2391<=v_2398 & v_2305=v_2398 & S1_2308=S1_2401 & S!=() & S=union(S1_2308,
  {v_2305})))))))))) --> INS2(S,S1_2389,a_2390),
 (exists(S2_2371:exists(v:exists(S2:exists(S1_2435:exists(v_2337:exists(v_2432:exists(S1_2308:exists(v_2305:S2_2371!=() & 
  S2_2371=S1_2435 & v=v_2337 & S2=union(S1_2435,{v_2432}) & (1+
  v_2432)<=v_2337 & v_2305=v_2432 & S1_2308=S_2336 & 
  INS2(S_2336,S1_2372,a_2373) & S=union(S1_2308,{v_2305}) & 
  S!=()))))))))) --> INS2(S,S1_2430,a_2431)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
Context of Verification Failure: File "sll_msb.ss",Line:315,Col:10
Last Proving Location: File "sll_msb.ss",Line:320,Col:21

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 70::
                                EXISTS(n_84,S_85,n_86,S1,
                                S2: x::sll1<n_84,S_85>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                res::sll1<n_86,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([S=S_85 & CPY(S,S2)][n=n_86 & n=n_84]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 70::
                              EXISTS(n_2615,S_2616,n_2617,S1_2618,
                              S2_2619: x::sll1<n_2615,S_2616>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              res::sll1<n_2617,S1_2618>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([n=n_2615 & n=n_2617 & 0<=n]
                               [S=S_2616 & CPY(S,S2_2619)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S_85:S_85=S & S_85=)) --> CPY(S,S2_2598),
 (exists(S1_2529:exists(S_85:exists(S1:exists(S1_2552:exists(S1_2539:exists(v_2549:exists(v_2536:exists(S1_2501:exists(v_2498:S1_2529=S1_2552 & 
  S_85=union(S1_2539,{v_2536}) & S1=union(S1_2552,{v_2549}) & 
  S1_2539=S1_2501 & S_2505=S1_2501 & v_2549=v_2536 & v_2498=v_2536 & 
  CPY(S_2505,S2_2530) & S=union(S1_2501,{v_2498}) & 
  S!=())))))))))) --> CPY(S,S2_2535),
 (exists(S_85:S_85= & S=S_85)) --> CPY(S,S2_2598)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FIL(S,S2)
!!! POST:  S=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 73::
                                EXISTS(m,
                                S2: res::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([m<=n][FIL(S,S2)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 73::
                              res::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([S2=S][m<=n & 0<=n]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(r_2709:exists(tmp_83':exists(x:exists(res:exists(m_2710:exists(m_2701:exists(n_2675:exists(n:exists(m:exists(v_bool_335_721':exists(v:exists(v_node_346_723':exists(v_bool_334_722':exists(m_2645:exists(S1_2646:exists(v_2643:exists(S1_2711:exists(v_2708:(r_2709=tmp_83' & 
  x=v_node_346_723' & res=v_node_346_723' & S2_2702=S1_2711 & 
  S1_2646=S_2676 & v_2643=v_2708 & 1+m_2710=m & 1+m_2701=m & n_2675=m_2645 & 
  -1+n=m_2645 & 0<=m & (-1+m)<=m_2645 & !(v_bool_335_721') & (1+v)<=v_2708 & 
  v_node_346_723'!=null & v_bool_334_722' & FIL(S_2676,S2_2702) & 
  0<=m_2645 | r_2709=tmp_83' & x=v_node_346_723' & res=v_node_346_723' & 
  S2_2702=S1_2711 & S1_2646=S_2676 & v_2643=v_2708 & 1+m_2710=m & 1+
  m_2701=m & n_2675=m_2645 & -1+n=m_2645 & 0<=m & (-1+m)<=m_2645 & 
  !(v_bool_335_721') & (1+v_2708)<=v & v_node_346_723'!=null & 
  v_bool_334_722' & FIL(S_2676,S2_2702) & 0<=m_2645) & S=union(S1_2646,
  {v_2643}) & S2=union(S1_2711,{v_2708}) & 
  S!=()))))))))))))))))))) --> FIL(S,S2),
 (S2= & S=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 67::
                                EXISTS(n_88,
                                S2: x::sll1<n_88,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([TRAV(S1,S2)][n=n_88]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 67::
                              x::sll1<n_88,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([S2=S1][n_88=n & 0<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_2806:exists(v_2803:exists(S1_2783:exists(v_2780:v_2803=v_2780 & 
  S1_2783=S1_2787 & S2_2802=S1_2806 & TRAV(S1_2787,S2_2802) & 
  S2=union(S1_2806,{v_2803}) & S1!=() & S1=union(S1_2783,
  {v_2780})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

Context of Verification Failure: File "sll_msb.ss",Line:107,Col:10
Last Proving Location: File "sll_msb.ss",Line:119,Col:11

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [MRG]
              EBase exists (Expl)(Impl)[n1; S1; n2; 
                    S2](ex)x1::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    x2::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                EXISTS(flted_107_113,
                                S3: res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([flted_107_113=n1+n2][MRG(S3,S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; S1; n2; 
                  S2](ex)x1::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  x2::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 21::
                              EXISTS(flted_107_3007,
                              S3_3008: res::sll1<flted_107_3007,S3_3008>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([MRG(S3_3008,S1,S2)]
                               [flted_107_3007=n1+n2 & 0<=n1 & 0<=n2]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_114_1004':exists(flted_107_113:exists(v_bool_109_1018':exists(x1:exists(x2:exists(v_bool_113_1017':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_114_1004'=x2 & flted_107_113=n2 & n2<=-1 & 
  v_bool_109_1018'<=0 & x1=null & x2!=null & 1<=v_bool_113_1017' | res=x2 & 
  S2=S3 & n1=0 & v_node_114_1004'=x2 & flted_107_113=n2 & 
  v_bool_109_1018'<=0 & x1=null & x2!=null & 1<=v_bool_113_1017' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(INS:exists(S1_2908:exists(a_2909:exists(S:exists(S1_2878:exists(v_2875:S1_2908=S1_2926 & 
  S3_2964!=() & S1_2908!=() & S1_2878!=() & INS(S,S1_2908,a_2909) & 
  S2_2928=S1_2878 & S3=S3_2964 & S=S1 & S1!=() & S2=union(S1_2878,
  {v_2875}) & S2!=()))))))) --> MRG(S3,S1,S2),
 (exists(INS:exists(a_2909:exists(S:exists(S1_2908:exists(S1_2878:exists(v_2875:S1_2908!=() & 
  S1_2878= & INS(S,S1_2908,a_2909) & S=S1 & S1_2908=S3 & S2=union(S1_2878,
  {v_2875}) & S2!=() & S1!=()))))))) --> MRG(S3,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; 
                    S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0!=m][S1!=()]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_93_115,
                                S2: x'::sll1<flted_93_115,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([1+flted_93_115=m][PF(S1,S2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S1!=()][(m+1)<=0 & x!=null | x!=null & 1<=m]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::sll1<flted_93_115,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (([1+flted_93_115=m & 0<=m][S2<subset> S1 ]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_116':exists(r_3030:exists(x':exists(x:exists(flted_93_115:exists(next_97_1033':exists(v_node_98_1034':exists(m_3031:exists(S1_3032:exists(v_3029:(-1+
  m=m_3031 & S1_3032=S2 & res=v_node_98_1034' & tmp_116'=v_node_98_1034' & 
  r_3030=x' & x=v_node_98_1034' & flted_93_115=m_3031 & m_3031<=-2 & 
  next_97_1033'=null & v_node_98_1034'!=null | -1+m=m_3031 & S1_3032=S2 & 
  res=v_node_98_1034' & tmp_116'=v_node_98_1034' & r_3030=x' & 
  x=v_node_98_1034' & flted_93_115=m_3031 & next_97_1033'=null & 
  v_node_98_1034'!=null & 0<=m_3031) & S1=union(S1_3032,{v_3029}) & 
  S1!=()))))))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Context of Verification Failure: File "sll_msb.ss",Line:82,Col:10
Last Proving Location: File "sll_msb.ss",Line:97,Col:2

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([forall(a:a <notin> S  | v<=a)][true]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(flted_82_118,
                                S1: x'::sll1<flted_82_118,S1>@M[Orig][LHSCase]@ rem br[{383}]&
                                (
                                ([-1+flted_82_118=n][S1!=() & PUF(S1,S,v)]
                                 [null!=x']))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ([forall(a:a <notin> S  | v<=a)]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              EXISTS(flted_82_3081,
                              S1_3082: x'::sll1<flted_82_3081,S1_3082>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([null!=x'][S1_3082!=() & PUF(S1_3082,S,v)]
                               [-1+flted_82_3081=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3068:exists(v_3065:v=v_3065 & S1_3068=S & forall(a:a <notin> S
   | v<=a) & S1=union(S1_3068,{v_3065})))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
( ) :sll_msb.ss:145: 10: Postcondition cannot be derived from context


(Cause of PostCond Failure):sll_msb.ss:145: 10:  List of Partial Context: [PC(1, 0)]
Failed States:
[
 Label: 
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 15.4 no match for rhs data node: x (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]
Successful States:


Context of Verification Failure: File "sll_msb.ss",Line:145,Col:10
Last Proving Location: File "sll_msb.ss",Line:149,Col:6

ERROR: at sll_msb.ss_145_10 
Message: Post condition cannot be derived by the system.
 
Procedure set_next$node~node FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure set_next$node~node

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([(1+a)<=n & 1<=a][null!=x][S!=()]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::ref [x]
                                EXISTS(n1,n2,S1,
                                S2: x'::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{383}] * 
                                res::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                                (
                                ([0!=n1 & 0!=n2 & n=n1+n2]
                                 [S1!=() & S2!=() & SPLIT(S,S1,S2)][null!=x']
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S](ex)x::sll1<n,S>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([S!=()][x!=null][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 84::ref [x]
                              x'::sll1<n1,S1>@M[Orig][LHSCase]@ rem br[{383}] * 
                              res::sll1<n2,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([S1!=() & S2!=() & union(S1,S2)=S][null!=res]
                               [null!=x'][0!=n1 & 0<=n & n=n1+n2 & 0!=n2]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_3301:exists(v_3298:exists(S1_3383:exists(v_3380:S1_3301!=() & 
  S1_3383= & v_3298=v_3380 & S2=S1_3301 & S=union(S1_3301,{v_3298}) & 
  S1=union(S1_3383,{v_3380}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_388_678':exists(tmp_78':exists(xnext_3411:exists(m_3415:exists(m_3339:exists(a:exists(n:exists(n_3341:exists(n1_3407:exists(n2_3408:exists(x':exists(v_bool_377_679':exists(x:exists(res:exists(r_3414:exists(r_3338:exists(a_3412:exists(n1:exists(n2:exists(S1_3416:exists(v_3413:exists(S1_3340:exists(v_3337:S1_3409!=() & 
  S2_3410!=() & S1_3340!=() & (v_node_388_678'=res & tmp_78'=res & 
  xnext_3411=r_3414 & 1+m_3415=n1 & m_3339=-1+n1+n2 & -1+a=a_3412 & n=n1+
  n2 & n_3341=-1+n1+n2 & 1+n1_3407=n1 & n2_3408=n2 & S2_3410=S2 & 
  S1_3409=S1_3416 & S1_3340=S_3342 & v_3413=v_3337 & x'=x & n2<=-1 & 
  !(v_bool_377_679') & x!=null & res!=null & r_3414!=null & r_3338!=null & 
  1<=a_3412 & a_3412<=(-2+n1+n2) & SPLIT(S_3342,S1_3409,S2_3410) | 
  v_node_388_678'=res & tmp_78'=res & xnext_3411=r_3414 & n1=0 & m_3415=-1 & 
  1+m_3339=n2 & -1+a=a_3412 & n=n2 & 1+n_3341=n2 & n1_3407=-1 & n2_3408=n2 & 
  S2_3410=S2 & S1_3409=S1_3416 & S1_3340=S_3342 & v_3413=v_3337 & x'=x & 
  1<=a_3412 & (2+a_3412)<=n2 & !(v_bool_377_679') & x!=null & res!=null & 
  r_3414!=null & r_3338!=null & SPLIT(S_3342,S1_3409,S2_3410) | 
  v_node_388_678'=res & tmp_78'=res & xnext_3411=r_3414 & 1+m_3415=n1 & 
  m_3339=-1+n1+n2 & -1+a=a_3412 & n=n1+n2 & n_3341=-1+n1+n2 & 1+n1_3407=n1 & 
  n2_3408=n2 & S2_3410=S2 & S1_3409=S1_3416 & S1_3340=S_3342 & 
  v_3413=v_3337 & x'=x & !(v_bool_377_679') & x!=null & res!=null & 
  r_3414!=null & r_3338!=null & 2<=n1 & 1<=a_3412 & a_3412<=(-2+n1+n2) & 
  SPLIT(S_3342,S1_3409,S2_3410) & 1<=n2) & S!=() & S1=union(S1_3416,
  {v_3413}) & S=union(S1_3340,
  {v_3337}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! REL :  SWAP(S1,S2,S3,S4)
!!! POST:  S1=S4 & S2=S3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SWAP]
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                    y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                    ([true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_120,n_121,S3,
                                S4: x'::sll1<m_120,S3>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                                y'::sll1<n_121,S4>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (([SWAP(S1,S2,S3,S4)][m=m_120][n=n_121]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::sll1<n,S1>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                  y::sll1<m,S2>@M[Orig][LHSCase]@ rem br[{384,383}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::sll1<m_120,S3>@M[Orig][LHSCase]@ rem br[{384,383}] * 
                              y'::sll1<n_121,S4>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([S3=S2][S4=S1][n_121=n & 0<=n][m_120=m & 0<=m]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S3=S2 & S4=S1) --> SWAP(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


20 false contexts at: ( (159,13)  (159,4)  (339,10)  (339,6)  (338,10)  (338,6)  (36,17)  (36,24)  (37,7)  (37,14)  (286,4)  (286,11)  (291,4)  (291,11)  (290,10)  (290,4)  (289,9)  (289,13)  (289,4)  (289,4) )

Total verification time: 13.31 second(s)
	Time spent in main process: 2.3 second(s)
	Time spent in child processes: 11.01 second(s)
