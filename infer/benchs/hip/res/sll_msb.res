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
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              
                              r_1386::node<v_1422,r_1423>@M[Orig][] * 
                              x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([a=1][r_1423=r_1537_1647]
                               [m_1538_1641=m_1424_1640 & -1+m=m_1424_1640 & 
                                 0<=n & -1+m_1387_1639=m_1424_1640 & -2+
                                 n=m_1424_1640 & 0<=m_1424_1640]
                               [x!=null][r_1386!=null]
                               [S1_1425_1645=S1_1539_1646 & 
                                 v_1536_1643=v_1385_1644 & 
                                 S=union(S1_1388_1642,{v_1385_1644}) & 
                                 S1_1388_1642!=() & S1=union(S1_1539_1646,
                                 {v_1536_1643}) & S!=() & DEL(S,S1) & 
                                 S1_1388_1642=union(S1_1425_1645,{v_1422})]
                               [v_bool_240_832_1649']))&
                              {FLOW,(20,21)=__norm}
                              or x::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([(m_1587_1650+1=0 & m=0 & m_1592_1651+
                                    1=0 & n=1+m_1470_1653 & a=1+
                                    v_int_244_1589_1652 & 
                                    n_1493_1654=m_1470_1653 & 
                                    S1_1593_1660=S1_1588_1661 & 
                                    v_1468_1658=v_1590_1659 & 
                                    S_1494_1656=S1_1471_1657 & 
                                    r_1469_1662=r_1591_1663 & 
                                    1<=v_int_244_1589_1652 & 
                                    v_int_244_1589_1652<m_1470_1653 & 
                                    !(v_bool_240_832_1664') & 
                                    r_1591_1663!=null & x!=null | m=1+
                                    m_1587_1650 & m_1592_1651=m_1587_1650 & 
                                    n=1+m_1470_1653 & a=1+
                                    v_int_244_1589_1652 & 
                                    n_1493_1654=m_1470_1653 & 
                                    S1_1593_1660=S1_1588_1661 & 
                                    v_1468_1658=v_1590_1659 & 
                                    S_1494_1656=S1_1471_1657 & 
                                    r_1469_1662=r_1591_1663 & 
                                    1<=v_int_244_1589_1652 & 
                                    v_int_244_1589_1652<m_1470_1653 & 
                                    !(v_bool_240_832_1664') & 
                                    1<=m_1587_1650 & x!=null & 
                                    r_1591_1663!=null) & S!=() & 0<=n & 
                                    S1=union(S1_1593_1660,{v_1590_1659}) & 
                                    DEL(S,S1) & 
                                    DEL(S_1494_1656,S1_1588_1661) & 
                                    S1_1471_1657!=() & S1_1588_1661!=() & 
                                    S=union(S1_1471_1657,{v_1468_1658})]
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(v_1422:exists(S1_1425:exists(S1_1388:exists(v_1385:exists(S1_1539:exists(v_1536:S1_1388!=() & 
  S1_1388=union(S1_1425,{v_1422}) & S1_1539=S1_1425 & v_1385=v_1536 & 
  S=union(S1_1388,{v_1385}) & S1=union(S1_1539,{v_1536}) & 
  S!=()))))))) --> DEL(S,S1),
 (exists(r_1469:exists(m_1470:exists(n_1493:exists(a:exists(m_1592:exists(m_1587:exists(v_int_244_1589:exists(n:exists(v_bool_240_832':exists(x:exists(r_1591:exists(m:exists(S1_1593:exists(v_1590:exists(S1_1471:exists(v_1468:S1_1471!=() & 
  S1_1588!=() & (r_1469=r_1591 & S1_1588=S1_1593 & S1_1471=S_1494 & 
  v_1590=v_1468 & 1+m_1470=n & 1+n_1493=n & -1+a=v_int_244_1589 & m=0 & 
  m_1592=-1 & m_1587=-1 & 1<=v_int_244_1589 & (2+v_int_244_1589)<=n & 
  !(v_bool_240_832') & x!=null & r_1591!=null & DEL(S_1494,S1_1588) | 
  r_1469=r_1591 & S1_1588=S1_1593 & S1_1471=S_1494 & v_1590=v_1468 & 1+
  m_1470=n & 1+n_1493=n & -1+a=v_int_244_1589 & 1+m_1592=m & 1+m_1587=m & 
  1<=v_int_244_1589 & (2+v_int_244_1589)<=n & !(v_bool_240_832') & x!=null & 
  r_1591!=null & DEL(S_1494,S1_1588) & 2<=m) & S!=() & S1=union(S1_1593,
  {v_1590}) & S=union(S1_1471,{v_1468})))))))))))))))))) --> DEL(S,S1)]
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
                              
                              res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([r_1728=tmp_92_1983']
                               [v_node_266_1896_1984=r_1899_1985]
                               [n_1784_1981=m_1729_1982 & 1+m_1900_1980=m & 
                                 0<=n & 0<=m_1729_1982 & (-1+
                                 m)<=m_1729_1982 & m_1729_1982<=m & 1+
                                 m_1823_1979=m & -1+n=m_1729_1982]
                               [v_node_267_803_1971'=x & 
                                 v_node_267_803_1971'=res & x!=null]
                               [v_1727=v_1898_1974 & 
                                 S1_1901_1975=S1_1825_1976 & 
                                 S_1785_1977=S1_1730_1978 & (1+
                                 v_1898_1974)<=v & DEL2(a_1952,S,S1) & 
                                 S!=() & S=union(S1_1730_1978,{v_1727}) & 
                                 DEL2(a_1824_1973,S_1785_1977,S1_1825_1976) & 
                                 S1=union(S1_1901_1975,{v_1898_1974})]
                               [v_bool_257_807_1988']
                               [!(v_bool_261_804_1987')]
                               [!(v_bool_258_805_1986')]))&
                              {FLOW,(20,21)=__norm}
                              or x::node<v_1727,r_1728>@M[Orig][] * 
                                 res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([(r_1728=v_node_262_797_1964' & 
                                    res=v_node_262_797_1964' & 
                                    m=m_1729_1967 & n=1+m_1729_1967 & 
                                    S1_1730_1966=S1 & v=v_1727 & 
                                    !(v_bool_258_805_1968') & (m_1729_1967+
                                    2)<=0 & v_bool_257_807_1970' & 
                                    v_bool_261_804_1969' & x!=null | 
                                    r_1728=v_node_262_797_1964' & 
                                    res=v_node_262_797_1964' & 
                                    m=m_1729_1967 & n=1+m_1729_1967 & 
                                    S1_1730_1966=S1 & v=v_1727 & 
                                    !(v_bool_258_805_1968') & 
                                    v_bool_257_807_1970' & 
                                    v_bool_261_804_1969' & x!=null & 
                                    0<=m_1729_1967) & S=union(S1_1730_1966,
                                    {v_1727}) & 0<=n & S!=() & 
                                    DEL2(a_1951,S,S1)]
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              or res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([r_1728=r_1842_1958]
                                  [m_1843_1954=m_1729_1961 & -1+
                                    n=m_1729_1961 & 0<=n & -1+
                                    m=m_1729_1961 & 0<=m_1729_1961]
                                  [v_node_259_791_1957'=x & 
                                    v_node_259_791_1957'=res & x!=null]
                                  [S1_1730_1960=S1_1844_1956 & 
                                    v_1727=v_1841_1955 & (1+
                                    v)<=v_1841_1955 & S=union(S1_1730_1960,
                                    {v_1727}) & S!=() & 
                                    S1=union(S1_1844_1956,{v_1841_1955}) & 
                                    DEL2(a_1950,S,S1)]
                                  [v_bool_257_807_1963']
                                  [v_bool_258_805_1962']))&
                                 {FLOW,(20,21)=__norm}
                              or res::sll1<m,S1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([n=0 & 0<=n][m=0][x=null]
                                  [v_null_270_806_1990'=null][res=null]
                                  [S= & DEL2(a_1953,S,S1) & S1=]
                                  [!(v_bool_257_807_1991')]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(v:exists(S1_1844:exists(v_1841:exists(S1_1730:exists(v_1727:(1+
  v)<=v_1841 & v_1727=v_1841 & S1_1844=S1_1730 & S1=union(S1_1844,
  {v_1841}) & S!=() & S=union(S1_1730,{v_1727}))))))) --> DEL2(a_1840,S,S1),
 (exists(v:exists(n:exists(r_1728:exists(res:exists(v_node_262_797':exists(m:exists(v_bool_258_805':exists(x:exists(v_bool_257_807':exists(v_bool_261_804':exists(m_1729:exists(S1_1730:exists(v_1727:(S1_1730=S1 & 
  v_1727=v & -1+n=m_1729 & r_1728=v_node_262_797' & res=v_node_262_797' & 
  m=m_1729 & v_bool_258_805'<=0 & m_1729<=-2 & x!=null & 
  1<=v_bool_257_807' & 1<=v_bool_261_804' | S1_1730=S1 & v_1727=v & -1+
  n=m_1729 & r_1728=v_node_262_797' & res=v_node_262_797' & m=m_1729 & 
  v_bool_258_805'<=0 & x!=null & 1<=v_bool_257_807' & 1<=v_bool_261_804' & 
  0<=m_1729) & S=union(S1_1730,{v_1727}) & 
  S!=())))))))))))))) --> DEL2(a_1883,S,S1),
 (exists(v:exists(S1_1901:exists(v_1898:exists(S1_1730:exists(v_1727:(1+
  v_1898)<=v & v_1727=v_1898 & S1_1730=S_1785 & S1_1825=S1_1901 & 
  DEL2(a_1824,S_1785,S1_1825) & S1=union(S1_1901,{v_1898}) & S!=() & 
  S=union(S1_1730,{v_1727}))))))) --> DEL2(a_1897,S,S1),
 (S1= & S=) --> DEL2(a_1946,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
!!! NEW RELS:[ (exists(res:exists(Anon_18:exists(r_2152:exists(v_node_362_695':exists(m_2153:exists(v:exists(v_bool_358_701':exists(x:exists(v_bool_361_700':exists(n:exists(S1_2154:exists(v_2151:(res=x & 
  Anon_18=r_2152 & m=v_2151 & v_node_362_695'=x & 1+m_2153=n & n<=-1 & 
  v<=v_2151 & v_bool_358_701'<=0 & x!=null & 1<=v_bool_361_700' | res=x & 
  Anon_18=r_2152 & m=v_2151 & v_node_362_695'=x & 1+m_2153=n & v<=v_2151 & 
  v_bool_358_701'<=0 & x!=null & 1<=v_bool_361_700' & 1<=n) & S!=() & 
  S=union(S1_2154,{v_2151})))))))))))))) --> FGE(S,m),
 (exists(v:exists(S1_2154:exists(v_2151:(1+v_2151)<=v & S1_2154=S_2191 & 
  m_2237=m & v<=m & FGE(S_2191,m_2237) & S=union(S1_2154,{v_2151}) & 
  S!=())))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
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
!!! NEW RELS:[ (exists(tmp_111':exists(res:exists(r_2399:exists(v_node_136_990':exists(n:exists(flted_132_110:exists(x:exists(flted_132_109:exists(next_135_989':exists(x':exists(m_2400:exists(S1_2401:exists(v_2398:(tmp_111'=v_node_136_990' & 
  res=v_node_136_990' & r_2399=v_node_136_990' & v=v_2398 & S1_2401=S2 & -1+
  n=m_2400 & flted_132_110=next_135_989' & x=x' & flted_132_109=m_2400 & 
  m_2400<=-2 & next_135_989'=null & x'!=null | tmp_111'=v_node_136_990' & 
  res=v_node_136_990' & r_2399=v_node_136_990' & v=v_2398 & S1_2401=S2 & -1+
  n=m_2400 & flted_132_110=next_135_989' & x=x' & flted_132_109=m_2400 & 
  next_135_989'=null & x'!=null & 0<=m_2400) & S=union(S1_2401,{v_2398}) & 
  S!=())))))))))))))) --> GN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                    (failure_code=15.3)  v_node_187_906'=r_2465 & v_node_187_906'=null |-  v_node_187_906'!=null (must-bug).
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
                  ([S!=()][0!=n][null!=x]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_185_2508,
                              S2_2509: res::sll1<flted_185_2508,S2_2509>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([GNN(S,S2_2509)][2+flted_185_2508=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
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
!!! NEW RELS:[ (exists(r_2530:exists(res:exists(v_node_169_934':exists(n:exists(flted_167_103:exists(x:exists(m_2531:exists(S1_2532:exists(v_2529:(r_2530=v_node_169_934' & 
  res=v_node_169_934' & S1_2532=S1 & -1+n=m_2531 & flted_167_103=m_2531 & 
  m_2531<=-2 & x!=null | r_2530=v_node_169_934' & res=v_node_169_934' & 
  S1_2532=S1 & -1+n=m_2531 & flted_167_103=m_2531 & x!=null & 0<=m_2531) & 
  S!=() & S=union(S1_2532,{v_2529}))))))))))) --> GT(S,S1)]
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
                              
                              res::sll1<flted_195_96,S1>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([r_2588_2835=r_2702_2822]
                               [res=v_node_204_885_2823' & 
                                 v_node_204_885_2823'!=null]
                               [x=r_2695_2824 & r_2695_2824!=null]
                               [m_2696_2829=n & 1+m_2589_2834=n & 0<=n & 1+
                                 m_2703_2830=n & -1+flted_195_96=n & 1<=n]
                               [S1_2704_2828=S1_2590_2833 & v=v_2694_2827 & 
                                 v_2587_2832=v_2701_2826 & S!=() & 
                                 S=union(S1_2590_2833,{v_2587_2832}) & 
                                 S1=union(S1_2697_2825,{v_2694_2827}) & 
                                 S1!=() & INS(S,S1,a_2812) & 
                                 v_2694_2827<=v_2701_2826 & 
                                 S1_2697_2825=union(S1_2704_2828,
                                 {v_2701_2826})]
                               [v_bool_203_892_2837']
                               [!(v_bool_199_893_2836')]))&
                              {FLOW,(20,21)=__norm}
                              or res::sll1<flted_195_96,S1>@M[Orig][LHSCase]@ rem br[{383}]&
                                 (
                                 ([m_2680_2816=0][flted_195_96=1][n=0 & 0<=n]
                                  [x=null][v_null_200_2676_2818=null]
                                  [r_2679_2819=null]
                                  [res=v_node_200_881_2817' & 
                                    v_node_200_881_2817'!=null]
                                  [v=v_2678_2815 & S1_2681_2814= & 
                                    S1=union(S1_2681_2814,{v_2678_2815}) & 
                                    S1!=() & S= & INS(S,S1,a_2811)]
                                  [v_bool_199_893_2821']))&
                                 {FLOW,(20,21)=__norm}
                              or res::sll1<flted_195_96,S1>@M[Orig][LHSCase]@ rem br[{383}]&
                                 (
                                 ([r_2588_2853=tmp_97_2854']
                                  [v_node_208_2759_2838=r_2762_2839 & 
                                    r_2762_2839!=null]
                                  [v_node_209_891_2840'=x & 
                                    v_node_209_891_2840'=res & x!=null]
                                  [1+m_2763_2852=flted_195_96 & 0<=n & 1+
                                    n=flted_195_96 & 2+
                                    m_2589_2850=flted_195_96 & 
                                    2<=flted_195_96 & 1+
                                    flted_195_2663_2851=flted_195_96 & 2+
                                    n_2626_2849=flted_195_96]
                                  [v_2587_2843=v_2761_2844 & 
                                    S_2627_2845=S1_2590_2846 & 
                                    S1_2764_2847=S1_2664_2848 & (1+
                                    v_2761_2844)<=v & S1_2664_2848!=() & 
                                    S1=union(S1_2764_2847,{v_2761_2844}) & 
                                    INS(S,S1,a_2813) & 
                                    INS(S_2627_2845,S1_2664_2848,a_2665_2842) & 
                                    S!=() & S1!=() & S=union(S1_2590_2846,
                                    {v_2587_2843})]
                                  [!(v_bool_203_892_2856')]
                                  [!(v_bool_199_893_2855')]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(v:exists(S1_2681:exists(v_2678:S1_2681= & v_2678=v & S= & 
  S1=union(S1_2681,{v_2678}))))) --> INS(S,S1,a_2677),
 (exists(v_2701:exists(v:exists(S1_2704:exists(S1_2697:exists(v_2694:exists(S1_2590:exists(v_2587:S1_2697=union(S1_2704,
  {v_2701}) & v_2694<=v_2701 & v_2587=v_2701 & v=v_2694 & S1_2590=S1_2704 & 
  S1=union(S1_2697,{v_2694}) & S=union(S1_2590,{v_2587}) & 
  S!=())))))))) --> INS(S,S1,a_2693),
 (exists(v:exists(S1_2590:exists(v_2587:exists(S1_2764:exists(v_2761:S1_2664!=() & 
  (1+v_2761)<=v & v_2587=v_2761 & S1_2590=S_2627 & S1_2664=S1_2764 & 
  INS(S_2627,S1_2664,a_2665) & S=union(S1_2590,{v_2587}) & S1=union(S1_2764,
  {v_2761}) & S!=())))))) --> INS(S,S1,a_2760)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
                              
                              res::sll1<flted_217_94,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([r_2936_3185=r_3062_3186]
                               [v_node_225_859_3187'=vn & 
                                 v_node_225_859_3187'=res & vn!=null]
                               [x=r_3055_3188 & r_3055_3188!=null]
                               [m_3056_3193=n & 1+m_2937_3198=n & 0<=n & 1+
                                 m_3063_3194=n & -1+flted_217_94=n & 1<=n]
                               [S1_3064_3192=S1_2938_3197 & v=v_3054_3190 & 
                                 v_2935_3195=v_3061_3191 & S2!=() & 
                                 v_3054_3190<=v_3061_3191 & 
                                 S2=union(S1_3057_3189,{v_3054_3190}) & 
                                 S=union(S1_2938_3197,{v_2935_3195}) & 
                                 S!=() & INS2(S,S1_3173,a_3174) & 
                                 S1_3057_3189=union(S1_3064_3192,
                                 {v_3061_3191})]
                               [v_bool_223_867_3200']
                               [!(v_bool_219_868_3199')]))&
                              {FLOW,(20,21)=__norm}
                              or res::sll1<flted_217_94,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                                 (
                                 ([m_3039_3179=0][flted_217_94=1][n=0 & 0<=n]
                                  [r_3038_3181=null][x=null]
                                  [next_220_849_3180'=null]
                                  [vn=v_node_221_850_3182' & vn=res & 
                                    v_node_221_850_3182'!=null]
                                  [v=v_3037_3178 & S1_3040_3177= & 
                                    S2=union(S1_3040_3177,{v_3037_3178}) & 
                                    S2!=()]
                                  [S= & INS2(S,S1_3171,a_3172)]
                                  [v_bool_219_868_3184']))&
                                 {FLOW,(20,21)=__norm}
                              or res::sll1<flted_217_94,S2>@M[Orig][LHSCase]@ rem br[{383}]&
                                 (
                                 ([vn!=null]
                                  [v_node_229_866_3201'=x & 
                                    v_node_229_866_3201'=res & x!=null]
                                  [1+m_3124_3215=flted_217_94 & 0<=n & 1+
                                    n=flted_217_94 & 2+
                                    m_2937_3213=flted_217_94 & 
                                    2<=flted_217_94 & 1+
                                    flted_217_3022_3214=flted_217_94 & 2+
                                    n_2979_3212=flted_217_94]
                                  [v_node_228_3119_3216=r_3123_3217 & 
                                    r_3123_3217!=null]
                                  [S1_3125_3204=S2_3023_3205 & 
                                    v_2935_3203=v_3122_3202 & 
                                    v=v_2981_3211 & 
                                    S_2980_3209=S1_2938_3210 & S2!=() & 
                                    INS2(S_2980_3209,S1_3024_3207,a_3025_3208) & 
                                    S2_3023_3205!=() & 
                                    INS2(S,S1_3175,a_3176) & (1+
                                    v_3122_3202)<=v_2981_3211 & 
                                    S=union(S1_2938_3210,{v_2935_3203}) & 
                                    S2=union(S1_3125_3204,{v_3122_3202}) & 
                                    S!=()]
                                  [Anon_17=Anon_2982_3218]
                                  [!(v_bool_223_867_3220')]
                                  [!(v_bool_219_868_3219')]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (S=) --> INS2(S,S1_3035,a_3036),
 (exists(v:exists(S2:exists(S1_3057:exists(v_3054:exists(v_3061:exists(S1_3064:exists(S1_2938:exists(v_2935:v=v_3054 & 
  S1_3057=union(S1_3064,{v_3061}) & S2=union(S1_3057,{v_3054}) & 
  v_3054<=v_3061 & v_2935=v_3061 & S1_2938=S1_3064 & S!=() & S=union(S1_2938,
  {v_2935})))))))))) --> INS2(S,S1_3052,a_3053),
 (exists(S2_3023:exists(v:exists(S2:exists(S1_3125:exists(v_2981:exists(v_3122:exists(S1_2938:exists(v_2935:S2_3023!=() & 
  S2_3023=S1_3125 & v=v_2981 & S2=union(S1_3125,{v_3122}) & (1+
  v_3122)<=v_2981 & v_2935=v_3122 & S1_2938=S_2980 & 
  INS2(S_2980,S1_3024,a_3025) & S=union(S1_2938,{v_2935}) & 
  S!=()))))))))) --> INS2(S,S1_3120,a_3121)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Context of Verification Failure: File "sll_msb.ss",Line:315,Col:10
Last Proving Location: File "sll_msb.ss",Line:320,Col:21

ERROR: at _0_0 
Message:  Error during Mona translation for var S2_3449

 
Procedure list_copy$node FAIL-2

Exception Failure(" Error during Mona translation for var S2_3449\n") Occurred!

Error(s) detected when checking procedure list_copy$node

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
!!! NEW RELS:[ (exists(r_3571:exists(tmp_83':exists(x:exists(res:exists(m_3572:exists(m_3561:exists(n_3531:exists(n:exists(m:exists(v_bool_335_721':exists(v:exists(v_node_346_723':exists(v_bool_334_722':exists(m_3487:exists(S1_3488:exists(v_3485:exists(S1_3573:exists(v_3570:(r_3571=tmp_83' & 
  x=v_node_346_723' & res=v_node_346_723' & S2_3562=S1_3573 & 
  S1_3488=S_3532 & v_3485=v_3570 & 1+m_3572=m & 1+m_3561=m & n_3531=m_3487 & 
  -1+n=m_3487 & 0<=m & (-1+m)<=m_3487 & !(v_bool_335_721') & (1+v)<=v_3570 & 
  v_node_346_723'!=null & v_bool_334_722' & FIL(S_3532,S2_3562) & 
  0<=m_3487 | r_3571=tmp_83' & x=v_node_346_723' & res=v_node_346_723' & 
  S2_3562=S1_3573 & S1_3488=S_3532 & v_3485=v_3570 & 1+m_3572=m & 1+
  m_3561=m & n_3531=m_3487 & -1+n=m_3487 & 0<=m & (-1+m)<=m_3487 & 
  !(v_bool_335_721') & (1+v_3570)<=v & v_node_346_723'!=null & 
  v_bool_334_722' & FIL(S_3532,S2_3562) & 0<=m_3487) & S=union(S1_3488,
  {v_3485}) & S2=union(S1_3573,{v_3570}) & 
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
 (exists(S1_3720:exists(v_3717:exists(S1_3691:exists(v_3688:v_3717=v_3688 & 
  S1_3691=S1_3697 & S2_3716=S1_3720 & TRAV(S1_3697,S2_3716) & 
  S2=union(S1_3720,{v_3717}) & S1!=() & S1=union(S1_3691,
  {v_3688})))))) --> TRAV(S1,S2),
 (S1=S2 & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...
Timeout when checking #simplify  Restarting Omega after ... 194 invocations Stop Omega... 194 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 195 invocations Stop Omega... 195 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 196 invocations Stop Omega... 196 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 197 invocations Stop Omega... 197 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 201 invocations Stop Omega... 201 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 203 invocations Stop Omega... 203 invocations Starting Omega...oc

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
                              
                              x2::node<v_3835,r_3836>@M[Orig][] * 
                              res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([v_node_204_885_2823_4360'=v_node_121_1015_4378' & 
                                 v_node_204_885_2823_4360'=res & 
                                 v_node_204_885_2823_4360'!=null]
                               [r_2702_2822_4362=r_2588_2835_4361]
                               [m_3837_4382=0 & 
                                 flted_195_96_4376=flted_107_113 & 
                                 m_2696_2829_4365=n_4377 & 
                                 m_2696_2829_4365=n1 & 0!=n1 & 0!=n2 & 
                                 0<=n2 & 1+m_2703_2830_4363=n_4377 & 
                                 flted_107_113=n1+n2 & -1+
                                 flted_195_96_4376=n_4377 & -1+
                                 n2=m_3837_4382 & 1<=n_4377 & 0<=n_4377 & 1+
                                 m_2589_2834_4364=n_4377]
                               [x1=r_2695_2824_4366 & null!=x1][x2!=null]
                               [r_3836=null]
                               [S1_2590_2833_4372=S1_2704_2828_4371 & 
                                 S_4381=S1 & S_4381=S3 & 
                                 v_3835=v_2694_2827_4373 & 
                                 v_2701_2826_4370=v_2587_2832_4369 & 
                                 S1_3838_4380= & S2=union(S1_3838_4380,
                                 {v_3835}) & S1!=() & 
                                 v_2694_2827_4373<=v_2701_2826_4370 & 
                                 S2!=() & S1=union(S1_2697_2825_4368,
                                 {v_2694_2827_4373}) & 
                                 S_4381=union(S1_2590_2833_4372,
                                 {v_2587_2832_4369}) & MRG(S3,S1,S2) & 
                                 INS(S_4381,S1,a_2812_4367) & 
                                 S1_2697_2825_4368=union(S1_2704_2828_4371,
                                 {v_2701_2826_4370})]
                               [v_bool_203_892_2837_4374']
                               [!(v_bool_199_893_2836_4375')]
                               [!(v_bool_113_1017_4383')]
                               [!(v_bool_109_1018_4384')]
                               [!(v_bool_118_1016_4385')]))&
                              {FLOW,(20,21)=__norm}
                              or x2::node<v_3835,r_3836>@M[Orig][] * 
                                 res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([r_2762_2839_4332=v_node_208_2759_2838_4331 & 
                                    r_2762_2839_4332!=null]
                                  [tmp_97_2854_4334'=r_2588_2853_4333]
                                  [x1=v_node_209_891_2840_4341' & null!=x1]
                                  [x2!=null]
                                  [flted_107_4187_4327=flted_107_113 & 
                                    m_3837_4353=n2_4036_4329 & n1=n_4340 & 
                                    n1_4034_4328=flted_195_96_4339 & -1+
                                    n2=m_3837_4353 & 
                                    0!=flted_107_4187_4327 & 0<=n2 & 
                                    0<=n2_4036_4329 & 2+
                                    m_2589_2850_4338=flted_195_96_4339 & 
                                    0!=n2 & 0<=n1_4034_4328 & 2+
                                    n_2626_2849_4336=flted_195_96_4339 & 1+
                                    flted_195_2663_2851_4337=flted_195_96_4339 & 
                                    0!=m_3837_4353 & 1+
                                    m_2763_2852_4335=flted_195_96_4339 & 1+
                                    n_4340=flted_195_96_4339 & 
                                    flted_107_113=n1+n2 & 0<=n_4340 & 
                                    0!=n1 & 2<=flted_195_96_4339 & 
                                    flted_107_4187_4327=n1_4034_4328+
                                    n2_4036_4329]
                                  [null!=r_3836]
                                  [res=v_node_119_1014_4330' & 
                                    null!=v_node_119_1014_4330']
                                  [v_2761_2844_4349=v_2587_2843_4348 & 
                                    S1_2590_2846_4352=S_2627_2845_4351 & 
                                    S1_2664_2848_4347=S1_2764_2847_4346 & 
                                    S_4350=S1 & S_4350=S1_4035_4325 & 
                                    S1_3838_4345=S2_4037_4326 & 
                                    S3_4188_4324=S3 & (1+
                                    v_2761_2844_4349)<=v_3835 & 
                                    S2=union(S1_3838_4345,{v_3835}) & 
                                    S1=union(S1_2764_2847_4346,
                                    {v_2761_2844_4349}) & MRG(S3,S1,S2) & 
                                    S1_2664_2848_4347!=() & 
                                    INS(S_2627_2845_4351,S1_2664_2848_4347,a_2665_2842_4342) & 
                                    S_4350=union(S1_2590_2846_4352,
                                    {v_2587_2843_4348}) & S2!=() & 
                                    S3_4188_4324!=() & 
                                    INS(S_4350,S1,a_2813_4344) & 
                                    S1_3838_4345!=() & S1!=() & 
                                    MRG(S3_4188_4324,S1_4035_4325,S2_4037_4326)]
                                  [v_bool_118_1016_4358']
                                  [!(v_bool_199_893_2855_4354')]
                                  [!(v_bool_203_892_2856_4355')]
                                  [!(v_bool_113_1017_4356')]
                                  [!(v_bool_109_1018_4357')]))&
                                 {FLOW,(20,21)=__norm}
                              or x2::node<v_3835,r_3836>@M[Orig][] * 
                                 res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([v_node_204_885_2823_4298'!=null]
                                  [r_2702_2822_4300=r_2588_2835_4299]
                                  [x1=r_2695_2824_4304 & null!=x1][x2!=null]
                                  [flted_107_4158_4291=flted_107_113 & 
                                    m_3837_4319=n2_4036_4296 & 
                                    m_2696_2829_4303=n_4315 & 
                                    m_2696_2829_4303=n1 & 
                                    flted_195_96_4314=n1_4034_4295 & 
                                    0<=n1_4034_4295 & 
                                    0!=flted_107_4158_4291 & 0<=n2 & -1+
                                    flted_195_96_4314=n_4315 & 
                                    0<=n2_4036_4296 & 0<=n_4315 & 
                                    flted_107_113=n1+n2 & 1+
                                    m_2589_2834_4302=n_4315 & 1+
                                    m_2703_2830_4301=n_4315 & 1<=n_4315 & -1+
                                    n2=m_3837_4319 & 
                                    flted_107_4158_4291=n1_4034_4295+
                                    n2_4036_4296 & 0!=m_3837_4319 & 0!=n2 & 
                                    0!=n1]
                                  [null!=r_3836]
                                  [res=v_node_119_1014_4297' & 
                                    null!=v_node_119_1014_4297']
                                  [S1_3838_4317=S2_4037_4294 & 
                                    S3_4159_4290=S3 & S_4318=S1 & 
                                    S_4318=S1_4035_4293 & 
                                    S1_2590_2833_4310=S1_2704_2828_4309 & 
                                    v_2701_2826_4308=v_2587_2832_4307 & 
                                    v_3835=v_2694_2827_4311 & 
                                    S3_4159_4290!=() & 
                                    v_2694_2827_4311<=v_2701_2826_4308 & 
                                    S_4318=union(S1_2590_2833_4310,
                                    {v_2587_2832_4307}) & S2!=() & 
                                    INS(S_4318,S1,a_2812_4305) & 
                                    S1_2697_2825_4306=union(S1_2704_2828_4309,
                                    {v_2701_2826_4308}) & 
                                    S1=union(S1_2697_2825_4306,
                                    {v_2694_2827_4311}) & MRG(S3,S1,S2) & 
                                    S1!=() & S2=union(S1_3838_4317,
                                    {v_3835}) & S1_3838_4317!=() & 
                                    MRG(S3_4159_4290,S1_4035_4293,S2_4037_4294)]
                                  [v_bool_203_892_2837_4312']
                                  [v_bool_118_1016_4322']
                                  [!(v_bool_199_893_2836_4313')]
                                  [!(v_bool_113_1017_4320')]
                                  [!(v_bool_109_1018_4321')]))&
                                 {FLOW,(20,21)=__norm}
                              or res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([(n1=0 & n2=flted_107_113 & S2=S3 & 
                                    v_node_114_1004_4286'=x2 & res=x2 & 
                                    (flted_107_113+1)<=0 & 
                                    !(v_bool_109_1018_4289') & x1=null & 
                                    x2!=null & v_bool_113_1017_4288' | 
                                    n1=0 & n2=flted_107_113 & S2=S3 & 
                                    v_node_114_1004_4286'=x2 & res=x2 & 
                                    !(v_bool_109_1018_4289') & x1=null & 
                                    x2!=null & v_bool_113_1017_4288' & 
                                    1<=flted_107_113) & S1= & 0<=n1 & 
                                    S2!=() & 0<=n2 & MRG(S3,S1,S2)]
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              or res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([n1=flted_107_113 & 0<=n1][n2=0 & 0<=n2]
                                  [res=v_node_110_1003_4283' & res=x1]
                                  [x2=null][S1=S3 & S2= & MRG(S3,S1,S2)]
                                  [v_bool_109_1018_4285']))&
                                 {FLOW,(20,21)=__norm}
                              or x2::node<v_3835,r_3836>@M[Orig][] * 
                                 res::sll1<flted_107_113,S3>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                 (
                                 ([r_2762_2839_4388=v_node_208_2759_2838_4387 & 
                                    r_2762_2839_4388!=null]
                                  [tmp_97_2854_4390'=r_2588_2853_4389]
                                  [m_3837_4410=0 & n1=n_4396 & 
                                    flted_107_113=flted_195_96_4395 & 
                                    0!=n1 & 1+n_4396=flted_195_96_4395 & 
                                    0<=n2 & 1+
                                    flted_195_2663_2851_4393=flted_195_96_4395 & 
                                    2+n_2626_2849_4392=flted_195_96_4395 & 
                                    -1+n2=m_3837_4410 & 0<=n_4396 & 1+
                                    m_2763_2852_4391=flted_195_96_4395 & 
                                    flted_107_113=n1+n2 & 0!=n2 & 2+
                                    m_2589_2850_4394=flted_195_96_4395 & 
                                    2<=flted_195_96_4395]
                                  [v_node_209_891_2840_4398'=x1 & 
                                    v_node_209_891_2840_4398'=v_node_121_1015_4397' & 
                                    v_node_209_891_2840_4398'=res & null!=x1]
                                  [x2!=null][r_3836=null]
                                  [v_2761_2844_4406=v_2587_2843_4405 & 
                                    S1_2590_2846_4409=S_2627_2845_4408 & 
                                    S1_2664_2848_4404=S1_2764_2847_4403 & 
                                    S_4407=S1 & S_4407=S3 & S1_3838_4402= & 
                                    MRG(S3,S1,S2) & 
                                    S_4407=union(S1_2590_2846_4409,
                                    {v_2587_2843_4405}) & S1!=() & (1+
                                    v_2761_2844_4406)<=v_3835 & 
                                    S1_2664_2848_4404!=() & 
                                    S2=union(S1_3838_4402,{v_3835}) & 
                                    S2!=() & INS(S_4407,S1,a_2813_4401) & 
                                    INS(S_2627_2845_4408,S1_2664_2848_4404,a_2665_2842_4399) & 
                                    S1=union(S1_2764_2847_4403,
                                    {v_2761_2844_4406})]
                                  [!(v_bool_199_893_2855_4411')]
                                  [!(v_bool_203_892_2856_4412')]
                                  [!(v_bool_113_1017_4413')]
                                  [!(v_bool_109_1018_4414')]
                                  [!(v_bool_118_1016_4415')]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (S3=S1 & S2=) --> MRG(S3,S1,S2),
 (exists(res:exists(n1:exists(v_node_114_1004':exists(flted_107_113:exists(v_bool_109_1018':exists(x1:exists(x2:exists(v_bool_113_1017':exists(n2:(res=x2 & 
  S2=S3 & n1=0 & v_node_114_1004'=x2 & flted_107_113=n2 & n2<=-1 & 
  v_bool_109_1018'<=0 & x1=null & x2!=null & 1<=v_bool_113_1017' | res=x2 & 
  S2=S3 & n1=0 & v_node_114_1004'=x2 & flted_107_113=n2 & 
  v_bool_109_1018'<=0 & x1=null & x2!=null & 1<=v_bool_113_1017' & 1<=n2) & 
  S2!=() & S1=)))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2590_2833:exists(v_2587_2832:exists(S1_2704_2828:exists(v_2701_2826:exists(INS:exists(S:exists(a_2812:exists(S1_2697_2825:exists(v_2694_2827:exists(S1_3838:exists(v_3835:S1_2704_2828=S1_2590_2833 & 
  v_2587_2832=v_2701_2826 & S3_4159!=() & S1_3838!=() & S=union(S1_2590_2833,
  {v_2587_2832}) & S1_2697_2825=union(S1_2704_2828,{v_2701_2826}) & 
  v_2694_2827<=v_2701_2826 & v_2694_2827=v_3835 & S=S1_4035 & 
  S2_4037=S1_3838 & S3=S3_4159 & S=S1 & INS(S,S1,a_2812) & 
  S1=union(S1_2697_2825,{v_2694_2827}) & S2!=() & S2=union(S1_3838,
  {v_3835}) & S1!=())))))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2590_2846:exists(S_2627_2845:exists(a_2665_2842:exists(S1_2664_2848:exists(v_2587_2843:exists(INS:exists(S:exists(a_2813:exists(S1_2764_2847:exists(v_2761_2844:exists(S1_3838:exists(v_3835:S_2627_2845=S1_2590_2846 & 
  S1_2664_2848!=() & S3_4188!=() & S1_3838!=() & S=union(S1_2590_2846,
  {v_2587_2843}) & INS(S_2627_2845,S1_2664_2848,a_2665_2842) & (1+
  v_2761_2844)<=v_3835 & S1_2764_2847=S1_2664_2848 & 
  v_2587_2843=v_2761_2844 & S=S1_4035 & S2_4037=S1_3838 & S3=S3_4188 & 
  S=S1 & INS(S,S1,a_2813) & S1=union(S1_2764_2847,{v_2761_2844}) & S1!=() & 
  S2!=() & S2=union(S1_3838,{v_3835})))))))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2704_2828:exists(S1_2590_2833:exists(v_2587_2832:exists(v_2701_2826:exists(INS:exists(S:exists(a_2812:exists(S1_2697_2825:exists(v_2694_2827:exists(S1_3838:exists(v_3835:S1_2704_2828=S1_2590_2833 & 
  v_2587_2832=v_2701_2826 & S1_3838= & S1_2697_2825=union(S1_2704_2828,
  {v_2701_2826}) & S=union(S1_2590_2833,{v_2587_2832}) & 
  v_2694_2827<=v_2701_2826 & v_2694_2827=v_3835 & S=S1 & S=S3 & 
  INS(S,S1,a_2812) & S2!=() & S1=union(S1_2697_2825,{v_2694_2827}) & 
  S2=union(S1_3838,{v_3835}) & S1!=())))))))))))) --> MRG(S3,S1,S2),
 (exists(S1_2590_2846:exists(S_2627_2845:exists(a_2665_2842:exists(S1_2664_2848:exists(v_2587_2843:exists(INS:exists(S:exists(a_2813:exists(S1_3838:exists(v_3835:exists(S1_2764_2847:exists(v_2761_2844:S_2627_2845=S1_2590_2846 & 
  S=union(S1_2590_2846,{v_2587_2843}) & S1_3838= & S1_2664_2848!=() & 
  INS(S_2627_2845,S1_2664_2848,a_2665_2842) & (1+v_2761_2844)<=v_3835 & 
  S1_2764_2847=S1_2664_2848 & v_2587_2843=v_2761_2844 & S=S1 & S=S3 & 
  INS(S,S1,a_2813) & S2=union(S1_3838,{v_3835}) & S1=union(S1_2764_2847,
  {v_2761_2844}) & S2!=() & S1!=()))))))))))))) --> MRG(S3,S1,S2)]
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
!!! NEW RELS:[ (exists(m:exists(res:exists(tmp_116':exists(r_4764:exists(x':exists(x:exists(flted_93_115:exists(next_97_1033':exists(v_node_98_1034':exists(m_4765:exists(S1_4766:exists(v_4763:(-1+
  m=m_4765 & S1_4766=S2 & res=v_node_98_1034' & tmp_116'=v_node_98_1034' & 
  r_4764=x' & x=v_node_98_1034' & flted_93_115=m_4765 & m_4765<=-2 & 
  next_97_1033'=null & v_node_98_1034'!=null | -1+m=m_4765 & S1_4766=S2 & 
  res=v_node_98_1034' & tmp_116'=v_node_98_1034' & r_4764=x' & 
  x=v_node_98_1034' & flted_93_115=m_4765 & next_97_1033'=null & 
  v_node_98_1034'!=null & 0<=m_4765) & S1=union(S1_4766,{v_4763}) & 
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
                              x'::sll1<flted_82_118,S1>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([x=r_4809_4832]
                               [x'=tmp_119_4829' & tmp_119_4829'!=null]
                               [n=m_4810_4833 & -1+
                                 flted_82_118=m_4810_4833 & 0<=n & 
                                 -1<=m_4810_4833]
                               [v_4808_4831=v & S=S1_4811_4830 & 
                                 forall(a:a <notin> S  | v<=a) & 
                                 S1=union(S1_4811_4830,{v_4808_4831}) & 
                                 PUF(S1,S,v) & S1!=()]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4811:exists(v_4808:v=v_4808 & S1_4811=S & forall(a:a <notin> S
   | v<=a) & S1=union(S1_4811,{v_4808})))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

( ) :sll_msb.ss:145: 10: Postcondition cannot be derived from context


(Cause of PostCond Failure):sll_msb.ss:145: 10:  List of Partial Context: [PC(1, 0)]
Failed States:
[
 Label: 
 State:
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       FAIL_OR 
        
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
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

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
!!! NEW RELS:[ (exists(S1_5059:exists(v_5056:exists(S1_5171:exists(v_5168:S1_5059!=() & 
  S1_5171= & v_5056=v_5168 & S2=S1_5059 & S=union(S1_5059,{v_5056}) & 
  S1=union(S1_5171,{v_5168}) & S!=()))))) --> SPLIT(S,S1,S2),
 (exists(v_node_388_678':exists(tmp_78':exists(xnext_5216:exists(m_5220:exists(m_5108:exists(a:exists(n:exists(n_5116:exists(n1_5212:exists(n2_5213:exists(x':exists(v_bool_377_679':exists(x:exists(res:exists(r_5219:exists(r_5107:exists(a_5217:exists(n1:exists(n2:exists(S1_5221:exists(v_5218:exists(S1_5109:exists(v_5106:S1_5214!=() & 
  S2_5215!=() & S1_5109!=() & (v_node_388_678'=res & tmp_78'=res & 
  xnext_5216=r_5219 & 1+m_5220=n1 & m_5108=-1+n1+n2 & -1+a=a_5217 & n=n1+
  n2 & n_5116=-1+n1+n2 & 1+n1_5212=n1 & n2_5213=n2 & S2_5215=S2 & 
  S1_5214=S1_5221 & S1_5109=S_5117 & v_5218=v_5106 & x'=x & n2<=-1 & 
  !(v_bool_377_679') & x!=null & res!=null & r_5219!=null & r_5107!=null & 
  1<=a_5217 & a_5217<=(-2+n1+n2) & SPLIT(S_5117,S1_5214,S2_5215) | 
  v_node_388_678'=res & tmp_78'=res & xnext_5216=r_5219 & n1=0 & m_5220=-1 & 
  1+m_5108=n2 & -1+a=a_5217 & n=n2 & 1+n_5116=n2 & n1_5212=-1 & n2_5213=n2 & 
  S2_5215=S2 & S1_5214=S1_5221 & S1_5109=S_5117 & v_5218=v_5106 & x'=x & 
  1<=a_5217 & (2+a_5217)<=n2 & !(v_bool_377_679') & x!=null & res!=null & 
  r_5219!=null & r_5107!=null & SPLIT(S_5117,S1_5214,S2_5215) | 
  v_node_388_678'=res & tmp_78'=res & xnext_5216=r_5219 & 1+m_5220=n1 & 
  m_5108=-1+n1+n2 & -1+a=a_5217 & n=n1+n2 & n_5116=-1+n1+n2 & 1+n1_5212=n1 & 
  n2_5213=n2 & S2_5215=S2 & S1_5214=S1_5221 & S1_5109=S_5117 & 
  v_5218=v_5106 & x'=x & !(v_bool_377_679') & x!=null & res!=null & 
  r_5219!=null & r_5107!=null & 2<=n1 & 1<=a_5217 & a_5217<=(-2+n1+n2) & 
  SPLIT(S_5117,S1_5214,S2_5215) & 1<=n2) & S!=() & S1=union(S1_5221,
  {v_5218}) & S=union(S1_5109,
  {v_5106}))))))))))))))))))))))))) --> SPLIT(S,S1,S2)]
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

Total verification time: 86.56 second(s)
	Time spent in main process: 6.14 second(s)
	Time spent in child processes: 80.42 second(s)
