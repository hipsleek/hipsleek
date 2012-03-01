
Processing file "sll_mso.ss"
Parsing sll_mso.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
!!! REL :  CL(sm,lg,v)
!!! POST:  lg>=v & v=sm
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&(([0<=n]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 63::
                                                         true&(([null=res]))&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 64::
                                                         EXISTS(n_101,sm,
                                                         lg: res::sll1<n_101,sm,lg>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                                         (
                                                         ([sm<=lg & 
                                                            CL(sm,lg,v)]
                                                          [n=n_101 & 0<=n_101]
                                                          ))&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 65::
                                                         true&(())&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&(([0<=n]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 63::
                                                       true&(
                                                       ([res=null][0=n]))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 64::
                                                       EXISTS(n_1442,sm_1443,
                                                       lg_1444: res::sll1<n_1442,sm_1443,lg_1444>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                                       (
                                                       ([v=sm_1443 & 
                                                          v<=lg_1444]
                                                        [n=n_1442 & 
                                                          0<=n_1442 & 1<=n]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 65::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (sm=v & v<=lg) --> CL(sm,lg,v),
 (v=sm & lg=lg_1414 & sm<=sm_1413 & sm_1413<=lg_1414 & 
  CL(sm_1413,lg_1414,v)) --> CL(sm,lg,v)]
!!! NEW ASSUME:[ RELASS [CL]: ( CL(sm_1413,lg_1414,v)) -->  lg_1414<sm_1413 | v<=sm_1413 & sm_1413<=lg_1414]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
!!! REL :  DEL(sres,xs,lres,xl)
!!! POST:  xl>=xs & xl=lres & xs=sres
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll1<n,xs,xl>@M[Orig][LHSCase]@ rem br[{399}]&(
                    ([1<=a & (1+a)<=n][xs<=xl][null!=x]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(nres,sres,
                                lres: x::sll1<nres,sres,lres>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (
                                ([0<=nres & 1+nres=n]
                                 [sres<=lres & DEL(sres,xs,lres,xl)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll1<n,xs,xl>@M[Orig][LHSCase]@ rem br[{399}]&(
                  ([x!=null][xs<=xl][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(nres_1623,sres_1624,
                              lres_1625: x::sll1<nres_1623,sres_1624,lres_1625>@M[Orig][LHSCase]@ rem br[{400,399}]&
                              (
                              ([xl=lres_1625 & xs=sres_1624 & xs<=xl]
                               [0<=nres_1623 & 0<=n & 1+nres_1623=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sres=xs & lres=xl & xs<=xl) --> DEL(sres,xs,lres,xl),
 (xl_1552=xl & sres=xs & lres=lres_1595 & xs<=sres_1594 & 
  sres_1594<=lres_1595 & xs<=xs_1551 & xs_1551<=xl & 
  DEL(sres_1594,xs_1551,lres_1595,xl_1552)) --> DEL(sres,xs,lres,xl)]
!!! NEW ASSUME:[ RELASS [DEL]: ( DEL(sres_1594,xs_1551,lres_1595,xl_1552)) -->  xl_1552<xs_1551 | xs_1551<=xl_1552 & lres_1595<sres_1594 | 
xs_1551<=sres_1594 & sres_1594<=lres_1595 & xs_1551<=xl_1552]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
!!! REL :  DEL2(sres,xs,lres,xl)
!!! POST:  sres>=xs & xl>=sres & xl=lres
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll1<n,xs,xl>@M[Orig][LHSCase]@ rem br[{400,399}]&
                    (([0<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 55::
                                EXISTS(nres,sres,
                                lres: res::sll1<nres,sres,lres>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (
                                ([0<=nres & nres<=n & (-1+n)<=nres]
                                 [sres<=lres & DEL2(sres,xs,lres,xl)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll1<n,xs,xl>@M[Orig][LHSCase]@ rem br[{400,399}]&
                  (([0<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 55::
                              EXISTS(nres_1777,sres_1778,
                              lres_1779: res::sll1<nres_1777,sres_1778,lres_1779>@M[Orig][LHSCase]@ rem br[{400,399}]&
                              (
                              ([xl=lres_1779 & sres_1778<=xl & xs<=xl & 
                                 xs<=sres_1778]
                               [0<=nres_1777 & 0<=n & (-1+n)<=nres_1777 & 
                                 nres_1777<=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sres=xs & lres=xl & xs<=xl) --> DEL2(sres,xs,lres,xl),
 (lres=xl & xs<=sres & sres<=xl) --> DEL2(sres,xs,lres,xl),
 (xl_1685=xl & sres=xs & lres=lres_1711 & xs<=xs_1684 & xs_1684<=xl & 
  xs<=sres_1710 & sres_1710<=lres_1711 & 
  DEL2(sres_1710,xs_1684,lres_1711,xl_1685)) --> DEL2(sres,xs,lres,xl),
 (xs=sres & xl=lres & sres<=lres) --> DEL2(sres,xs,lres,xl)]
!!! NEW ASSUME:[ RELASS [DEL2]: ( DEL2(sres_1710,xs_1684,lres_1711,xl_1685)) -->  xl_1685<xs_1684 | xs_1684<=xl_1685 & lres_1711<sres_1710 | 
xs_1684<=sres_1710 & sres_1710<=lres_1711 & xs_1684<=xl_1685]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(m,sl2)
!!! POST:  sl2>=m
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; sm; 
                    sl](ex)x::sll2<n,sm,sl>@M[Orig][LHSCase]@ rem br[{398,397}]&
                    (([0<=n][sm<=sl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 95::
                                
                                true&(([null=res]))&{FLOW,(20,21)=__norm}
                                or EXISTS(p,k,sm2,m,
                                   sl2: res::node<m,p>@M[Orig][] * 
                                   p::sll2<k,sm2,sl2>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                   (
                                   ([sm2<=sl2 & FGE(m,sl2) & v<=m][res!=null]
                                    [0<=k]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; 
                  sl](ex)x::sll2<n,sm,sl>@M[Orig][LHSCase]@ rem br[{398,397}]&
                  (([0<=n][sm<=sl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 95::
                              
                              true&(([res=null][0<=n][sm<=sl]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(p_1931,k_1932,sm2_1933,m_1934,
                                 sl2_1935: res::node<m_1934,p_1931>@M[Orig][] * 
                                 p_1931::sll2<k_1932,sm2_1933,sl2_1935>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                 (
                                 ([sm2_1933<=sl2_1935 & v<=m_1934 & 
                                    m_1934<=sl2_1935]
                                  [0<=k_1932][res!=null][0<=n][sm<=sl]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (m<=sl2) --> FGE(m,sl2),
 (m=m_1924 & sl2=sl2_1925 & FGE(m_1924,sl2_1925)) --> FGE(m,sl2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(sres,xs,lres,xl)
!!! POST:  sres>=xs & lres>=sres & xl>=lres
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::ref [x]
                                EXISTS(flted_159_120,flted_159_121,lres,v,
                                sres: x'::node<v,flted_159_121>@M[Orig][] * 
                                res::sll2<flted_159_120,sres,lres>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([null=flted_159_121]
                                 [0<=flted_159_120 & 1+flted_159_120=n]
                                 [sres<=lres & v<=sres & xs<=v & 
                                   GN(sres,xs,lres,xl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 27::ref [x]
                              EXISTS(flted_159_1977,flted_159_1978,lres_1979,
                              v_1980,
                              sres_1981: x'::node<v_1980,flted_159_1978>@M[Orig][] * 
                              res::sll2<flted_159_1977,sres_1981,lres_1979>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([lres_1979<=xl & xs<=xl & v_1980<=sres_1981 & 
                                 xs<=sres_1981 & sres_1981<=lres_1979 & 
                                 xs<=v_1980]
                               [x'!=null]
                               [0<=flted_159_1977 & 0<=n & 1+flted_159_1977=n]
                               [null=flted_159_1978]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs<=sres & sres<=lres & lres<=xl) --> GN(sres,xs,lres,xl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1, n!=0]
!!! REL :  GNN(sm1,lg1,sm2,lg2)
!!! POST:  sm2>=sm1 & lg2>=sm2 & lg1>=lg2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[n; sm1; 
                    lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}]&
                    (([0<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(flted_215_110,sm2,
                                lg2: res::sll2<flted_215_110,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([0<=flted_215_110 & 2+flted_215_110=n]
                                 [sm2<=lg2 & GNN(sm1,lg1,sm2,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; 
                  lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}]&
                  (([0<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n | n<=(0-1)]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 39::
                              EXISTS(flted_215_2047,sm2_2048,
                              lg2_2049: res::sll2<flted_215_2047,sm2_2048,lg2_2049>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([lg2_2049<=lg1 & sm1<=lg1 & sm1<=sm2_2048 & 
                                 sm2_2048<=lg2_2049]
                               [0<=flted_215_2047 & 0<=n & 2+flted_215_2047=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm1<=sm2 & sm2<=lg2 & lg2<=lg1) --> GNN(sm1,lg1,sm2,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(sres,xs,lres,xl)
!!! POST:  sres>=xs & lres>=sres & xl>=lres
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                EXISTS(flted_195_114,sres,
                                lres: res::sll2<flted_195_114,sres,lres>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([0<=flted_195_114 & 1+flted_195_114=n]
                                 [sres<=lres & GT(sres,xs,lres,xl)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              EXISTS(flted_195_2082,sres_2083,
                              lres_2084: res::sll2<flted_195_2082,sres_2083,lres_2084>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([lres_2084<=xl & xs<=xl & xs<=sres_2083 & 
                                 sres_2083<=lres_2084]
                               [0<=flted_195_2082 & 0<=n & 1+flted_195_2082=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs<=sres & sres<=lres & lres<=xl) --> GT(sres,xs,lres,xl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
!!! REL :  CPY(sm1,lg1,sm2,lg2)
!!! POST:  lg1>=sm2 & lg1=lg2 & sm2=sm1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; sm1; 
                    lg1](ex)x::sll1<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{400,399}]&
                    (([0<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 80::
                                EXISTS(n_88,sm1_89,lg1_90,n_91,sm2,
                                lg2: x::sll1<n_88,sm1_89,lg1_90>@M[Orig][LHSCase]@ rem br[{400,399}] * 
                                res::sll1<n_91,sm2,lg2>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (
                                ([sm1=sm1_89 & lg1=lg1_90 & sm1_89<=lg1_90 & 
                                   sm2<=lg2 & CPY(sm1,lg1,sm2,lg2)]
                                 [n=n_91 & n=n_88 & 0<=n_91]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; 
                  lg1](ex)x::sll1<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{400,399}]&
                  (([0<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 80::
                              EXISTS(n_2566,sm1_2567,lg1_2568,n_2569,
                              sm2_2570,
                              lg2_2571: x::sll1<n_2566,sm1_2567,lg1_2568>@M[Orig][LHSCase]@ rem br[{400,399}] * 
                              res::sll1<n_2569,sm2_2570,lg2_2571>@M[Orig][LHSCase]@ rem br[{400,399}]&
                              (
                              ([lg1=lg1_2568 & lg1=lg2_2571 & sm1=sm1_2567 & 
                                 sm1=sm2_2570 & sm1<=lg1]
                               [n=n_2566 & n=n_2569 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm1=sm2 & lg1=lg1_2471 & lg2=lg2_2494 & sm2<=sm1_2470 & 
  sm1_2470<=lg1_2471 & sm2<=sm2_2493 & sm2_2493<=lg2_2494 & 
  CPY(sm1_2470,lg1_2471,sm2_2493,lg2_2494)) --> CPY(sm1,lg1,sm2,lg2),
 (sm1=sm2 & lg2=lg1 & sm2<=lg1) --> CPY(sm1,lg1,sm2,lg2)]
!!! NEW ASSUME:[ RELASS [CPY]: ( CPY(sm1_2470,lg1_2471,sm2_2493,lg2_2494)) -->  lg1_2471<sm1_2470 | sm1_2470<=lg1_2471 & lg2_2494<sm2_2493 | 
sm1_2470<=sm2_2493 & sm2_2493<=lg2_2494 & sm1_2470<=lg1_2471]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(xs,xl,sres,lres)
!!! POST:  sres>=xs & lres>=sres & lres=xl
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll1<n,xs,xl>@M[Orig][LHSCase]@ rem br[{400,399}]&
                    (([0<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::
                                EXISTS(nres,sres,
                                lres: res::sll1<nres,sres,lres>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (
                                ([0<=nres & nres<=n]
                                 [sres<=lres & FIL(xs,xl,sres,lres)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll1<n,xs,xl>@M[Orig][LHSCase]@ rem br[{400,399}]&
                  (([0<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 85::
                              EXISTS(nres_2717,sres_2718,
                              lres_2719: res::sll1<nres_2717,sres_2718,lres_2719>@M[Orig][LHSCase]@ rem br[{400,399}]&
                              (
                              ([xl=lres_2719 & sres_2718<=lres_2719 & 
                                 xs<=xl & xs<=sres_2718]
                               [0<=nres_2717 & 0<=n & nres_2717<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xl_2620=xl & sres=sres_2680 & lres=lres_2681 & xs<=xs_2619 & xs_2619<=xl & 
  sres_2680<=lres_2681 & 
  FIL(xs_2619,xl_2620,sres_2680,lres_2681)) --> FIL(xs,xl,sres,lres),
 (lres=lres_2668 & sres=xs & xl_2642=xl & xs<=sres_2667 & 
  sres_2667<=lres_2668 & xs<=xs_2641 & xs_2641<=xl & 
  FIL(xs_2641,xl_2642,sres_2667,lres_2668)) --> FIL(xs,xl,sres,lres),
 (xs=sres & xl=lres & sres<=lres) --> FIL(xs,xl,sres,lres)]
!!! NEW ASSUME:[ RELASS [FIL]: ( FIL(xs_2641,xl_2642,sres_2667,lres_2668)) -->  xs_2641<=sres_2667 | xl_2642<xs_2641 & sres_2667<xs_2641 | 
lres_2668<sres_2667 & sres_2667<xs_2641 & xs_2641<=xl_2642]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(sm1,lg1,sm2,lg2)
!!! POST:  lg2>=sm2 & lg2=lg1 & sm2=sm1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; sm1; 
                    lg1](ex)x::sll1<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{400,399}]&
                    (([0<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 77::
                                EXISTS(n_93,sm2,
                                lg2: x::sll1<n_93,sm2,lg2>@M[Orig][LHSCase]@ rem br[{400,399}]&
                                (
                                ([sm2<=lg2 & TRAV(sm1,lg1,sm2,lg2)]
                                 [n=n_93 & 0<=n_93]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; 
                  lg1](ex)x::sll1<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{400,399}]&
                  (([0<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 77::
                              EXISTS(n_2803,sm2_2804,
                              lg2_2805: x::sll1<n_2803,sm2_2804,lg2_2805>@M[Orig][LHSCase]@ rem br[{400,399}]&
                              (
                              ([lg1=lg2_2805 & sm1=sm2_2804 & sm1<=lg1]
                               [n=n_2803 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (lg1_2755=lg1 & lg2=lg2_2768 & sm2=sm1 & sm1<=sm1_2754 & sm1_2754<=lg1 & 
  sm1<=sm2_2767 & sm2_2767<=lg2_2768 & 
  TRAV(sm1_2754,lg1_2755,sm2_2767,lg2_2768)) --> TRAV(sm1,lg1,sm2,lg2),
 (sm1=sm2 & lg1=lg2 & sm2<=lg2) --> TRAV(sm1,lg1,sm2,lg2)]
!!! NEW ASSUME:[ RELASS [TRAV]: ( TRAV(sm1_2754,lg1_2755,sm2_2767,lg2_2768)) -->  lg1_2755<sm1_2754 | sm1_2754<=lg1_2755 & lg2_2768<sm2_2767 | 
sm1_2754<=sm2_2767 & sm2_2767<=lg2_2768 & sm1_2754<=lg1_2755]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
!!! REL :  MRG(sm1,sm2,sm3,lg1,lg2,lg3)
!!! POST:  sm3>=sm2 & lg3>=sm3 & lg2>=lg3 & lg1>=sm1 | sm3>=sm2 & sm1>=(1+sm3) & 
lg1>=sm1 & lg3>=lg1 & lg2>=sm3 | lg1>=sm1 & lg3>=lg1 & lg2>=sm2 & sm1=sm3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG]
              EBase exists (Expl)(Impl)[n1; sm1; lg1; n2; sm2; 
                    lg2](ex)x1::sll2<n1,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                    x2::sll2<n2,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&
                    (([0<=n1][sm1<=lg1][0<=n2][sm2<=lg2]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::
                                EXISTS(flted_135_124,sm3,
                                lg3: res::sll2<flted_135_124,sm3,lg3>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([0<=flted_135_124 & flted_135_124=n1+n2]
                                 [sm3<=lg3 & MRG(sm1,sm2,sm3,lg1,lg2,lg3)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n1; sm1; lg1; n2; sm2; 
                  lg2](ex)x1::sll2<n1,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                  x2::sll2<n2,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&(
                  ([0<=n1][0<=n2][sm1<=lg1][sm2<=lg2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::
                              EXISTS(flted_135_2936,sm3_2937,
                              lg3_2938: res::sll2<flted_135_2936,sm3_2937,lg3_2938>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([(sm3_2937>=sm2 & lg3_2938>=sm3_2937 & 
                                 lg2>=lg3_2938 & lg1>=sm1 | sm3_2937>=sm2 & 
                                 sm1>=(1+sm3_2937) & lg1>=sm1 & 
                                 lg3_2938>=lg1 & lg2>=sm3_2937 | lg1>=sm1 & 
                                 lg3_2938>=lg1 & lg2>=sm2 & sm1=sm3_2937) & 
                                 sm3_2937<=lg3_2938 & sm1<=lg1 & sm2<=lg2]
                               [0<=flted_135_2936 & 0<=n1 & 
                                 flted_135_2936=n1+n2 & 0<=n2]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm3=sm1 & lg3=lg1 & sm1<=lg1 & sm2<=lg2) --> MRG(sm1,sm2,sm3,lg1,lg2,lg3),
 (sm3=sm2 & lg3=lg2 & sm2<=lg2 & sm1<=lg1) --> MRG(sm1,sm2,sm3,lg1,lg2,lg3),
 ((sm1=sm1_2886 & sm3_2924=sm3 & lg3_2925=lg3 & sm1_2886<=lg1 & 
  lg1<=lg1_2887 & lg1_2887<=sm2_2889 & sm2_2889<=lg2_2890 & lg2_2890<=lg2 & 
  sm3<=lg3 & sm2<=lg1_2887 | lg1=lg1_2887 & sm3_2924=sm3 & lg3_2925=lg3 & 
  sm2<=sm1_2886 & sm1_2886<=sm2_2889 & sm2_2889<=lg2_2890 & lg2_2890<=lg2 & 
  sm1_2886<sm1 & sm1<=lg1_2887 & sm3<=lg3 | sm1=sm1_2886 & lg1=lg1_2887 & 
  sm3_2924=sm3 & lg3_2925=lg3 & sm1_2886<=sm2_2889 & sm2<=sm2_2889 & 
  sm2_2889<=lg2_2890 & lg2_2890<=lg2 & sm3<=lg3 & sm1_2886<lg1_2887 & 
  sm2<lg1_2887) & 
  MRG(sm1_2886,sm2_2889,sm3_2924,lg1_2887,lg2_2890,lg3_2925)) --> MRG(sm1,sm2,sm3,lg1,lg2,lg3),
 (sm1=sm3 & lg1<=lg3 & sm2<=lg3 & lg3<=lg2 & sm3<=lg1 | lg1=lg3 & sm2<=sm3 & 
  sm3<sm1 & sm1<=lg3 & sm3<=lg2 | lg1=lg3 & sm1=sm3 & sm3<=(lg3-1) & 
  sm3<=lg2 & sm2<=(lg3-1) & sm2<=lg2) --> MRG(sm1,sm2,sm3,lg1,lg2,lg3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(sm1,sm2,lg1,lg2)
!!! POST:  sm2>=sm1 & lg2>=sm2 & lg1>=lg2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; sm1; 
                    lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{397}]&
                    (([null!=x][0<=m & 0!=m][sm1<=lg1]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::ref [x]
                                EXISTS(flted_122_126,sm2,
                                lg2: x'::sll2<flted_122_126,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([0<=flted_122_126 & 1+flted_122_126=m]
                                 [sm2<=lg2 & PF(sm1,sm2,lg1,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; sm1; 
                  lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{397}]&
                  (([x!=null][1<=m][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 19::ref [x]
                              EXISTS(flted_122_2977,sm2_2978,
                              lg2_2979: x'::sll2<flted_122_2977,sm2_2978,lg2_2979>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([lg2_2979<=lg1 & sm1<=lg1 & sm1<=sm2_2978 & 
                                 sm2_2978<=lg2_2979]
                               [0<=flted_122_2977 & 0<=m & 1+flted_122_2977=m]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm1<=sm2 & sm2<=lg2 & lg2<=lg1) --> PF(sm1,sm2,lg1,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n; sm; 
                    lg](ex)x::sll2<n,sm,lg>@M[Orig][LHSCase]@ rem br[{398,397}]&
                    (([sm<=lg & PUF(v,sm)][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::ref [x]
                                EXISTS(flted_111_129,v1,
                                lg1: x'::sll2<flted_111_129,v1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([0<=flted_111_129 & -1+flted_111_129=n]
                                 [v1<=lg1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; 
                  lg](ex)x::sll2<n,sm,lg>@M[Orig][LHSCase]@ rem br[{398,397}]&
                  (([sm<=lg & v<=sm][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 17::ref [x]
                              EXISTS(flted_111_3009,v1_3010,
                              lg1_3011: x'::sll2<flted_111_3009,v1_3010,lg1_3011>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([1+n=flted_111_3009 & 0<=n & 0<=flted_111_3009]
                               [v1_3010<=lg1_3011][sm<=lg]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[ RELASS [PUF]: ( PUF(v,sm)) -->  v<=sm]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_null$node... 
Procedure ret_null$node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(v,sm2,sm3,lg3m_3050,lg2)
!!! POST:  sm2>=(sm3+1) & lg2>=sm2 & sm3=v | lg2>=sm3 & v>=sm3 & sm3=sm2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_13; sm1; lg1; j; sm2; 
                    lg2](ex)x::node<v,t>@M[Orig][] * 
                    t::sll2<Anon_13,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                    y::sll2<j,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&(
                    ([x!=null][sm1<=lg1][0<=Anon_13][0<=j][sm2<=lg2]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [x]
                                EXISTS(lg3,k,sm3,
                                lg3m: x'::sll2<k,sm3,lg3>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([0<=k & -1+k=j]
                                 [sm3<=lg3 & SN(v,sm2,sm3,lg3m,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_13; sm1; lg1; j; sm2; 
                  lg2](ex)x::node<v,t>@M[Orig][] * 
                  t::sll2<Anon_13,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                  y::sll2<j,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&(
                  ([x!=null][0<=j][sm1<=lg1][sm2<=lg2][0<=Anon_13]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              EXISTS(lg3_3055,k_3056,
                              sm3_3057: x'::sll2<k_3056,sm3_3057,lg3_3055>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([sm3_3057<=lg3_3055]
                               [0<=k_3056 & 0<=j & -1+k_3056=j][sm2<=lg2]
                               [sm1<=lg1][0<=Anon_13]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (v=sm3 & sm3<sm2 & sm2<=lg2 | sm2=sm3 & sm3<=lg2 & 
  sm3<=v) --> SN(v,sm2,sm3,lg3m_3050,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! REL :  SNULL(xs,v,sl_3087)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::ref [x]
                                EXISTS(flted_205_112,v,
                                sl: x'::node<v,flted_205_112>@M[Orig][]&(
                                ([null=flted_205_112][SNULL(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 37::ref [x]
                              EXISTS(flted_205_3088,
                              v_3089: x'::node<v_3089,flted_205_3088>@M[Orig][]&
                              (
                              ([x'!=null][null=flted_205_3088][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs<=v) --> SNULL(xs,v,sl_3087)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! REL :  SNULL2(xs,v,sl_3130)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL2]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 32::ref [x]
                                EXISTS(flted_182_116,v,
                                sl: x'::node<v,flted_182_116>@M[Orig][]&(
                                ([null=flted_182_116][SNULL2(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{397}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 32::ref [x]
                              EXISTS(flted_182_3131,
                              v_3132: x'::node<v_3132,flted_182_3131>@M[Orig][]&
                              (
                              ([x'!=null][null=flted_182_3131][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs<=v) --> SNULL2(xs,v,sl_3130)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; sm1; lg1; m; sm2; 
                    lg2](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                    y::sll2<m,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&(
                    ([0<=n][sm1<=lg1][0<=m][sm2<=lg2]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::ref [x;y]
                                EXISTS(m_131,n_132,smy2,lgy2,smx1,
                                lgx1: x'::sll2<m_131,smy2,lgy2>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                                y'::sll2<n_132,smx1,lgx1>@M[Orig][LHSCase]@ rem br[{398,397}]&
                                (
                                ([m=m_131 & 0<=m_131][n=n_132 & 0<=n_132]
                                 [smy2<=lgy2][smx1<=lgx1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; lg1; m; sm2; 
                  lg2](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                  y::sll2<m,sm2,lg2>@M[Orig][LHSCase]@ rem br[{398,397}]&(
                  ([0<=n][0<=m][sm1<=lg1][sm2<=lg2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 14::ref [x;y]
                              EXISTS(m_3414,smy2_3415,lgy2_3416,n_3417,
                              smx1_3418,
                              lgx1_3419: x'::sll2<m_3414,smy2_3415,lgy2_3416>@M[Orig][LHSCase]@ rem br[{398,397}] * 
                              y'::sll2<n_3417,smx1_3418,lgx1_3419>@M[Orig][LHSCase]@ rem br[{398,397}]&
                              (
                              ([n=n_3417 & 0<=n][m=m_3414 & 0<=m]
                               [lg2=lgy2_3416 & sm2=smy2_3415 & sm2<=lg2]
                               [lg1=lgx1_3419 & sm1=smx1_3418 & sm1<=lg1]
                               [y=x'][x=y']))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1759 invocations 
16 false contexts at: ( (187,13)  (187,4)  (54,17)  (54,24)  (55,7)  (55,14)  (323,4)  (323,11)  (328,4)  (328,11)  (327,10)  (327,4)  (326,9)  (326,13)  (326,4)  (326,4) )

Total verification time: 1.62 second(s)
	Time spent in main process: 0.45 second(s)
	Time spent in child processes: 1.17 second(s)
