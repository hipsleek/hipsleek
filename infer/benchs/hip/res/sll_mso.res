
Processing file "sll_mso.ss"
Parsing sll_mso.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
!!! REL :  CL(sm,lg,v)
!!! POST:  v>=sm & lg>=v
!!! PRE :  true
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
                                                         EXISTS(n_93,sm,
                                                         lg: res::sll2<n_93,sm,lg>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                                         (
                                                         ([sm<=lg & 
                                                            CL(sm,lg,v)]
                                                          [n=n_93 & 0<=n_93]))&
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
                           0<n -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 61::
                                                       EXISTS(n_1374,sm_1375,
                                                       lg_1376: res::sll2<n_1374,sm_1375,lg_1376>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                                       (
                                                       ([sm_1375<=lg_1376 & 
                                                          sm_1375<=v & 
                                                          v<=lg_1376]
                                                        [n=n_1374 & 
                                                          0<=n_1374 & 1<=n]
                                                        ))&
                                                       {FLOW,(20,21)=__norm}))
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 62::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (sm<=v & v<=lg) --> CL(sm,lg,v),
 (sm_1345<=lg_1346 & sm<=v & v<=sm_1345 & lg_1346<=lg & 
  CL(sm_1345,lg_1346,v)) --> CL(sm,lg,v)]
!!! NEW ASSUME:[ RELASS [CL]: ( CL(sm_1345,lg_1346,v)) -->  lg_1346<sm_1345 | v<=sm_1345 & sm_1345<=lg_1346]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(sres,xs,lres,xl)
!!! POST:  sres>=xs & lres>=sres & xl>=lres
!!! PRE :  xs<=xl
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::ref [x]
                                EXISTS(flted_143_112,flted_143_113,lres,v,
                                sres: x'::node<v,flted_143_113>@M[Orig][] * 
                                res::sll2<flted_143_112,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_143_113]
                                 [0<=flted_143_112 & 1+flted_143_112=n]
                                 [sres<=lres & v<=sres & xs<=v & 
                                   GN(sres,xs,lres,xl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][xs<=xl]))&{FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              EXISTS(flted_143_1972,flted_143_1973,lres_1974,
                              v_1975,
                              sres_1976: x'::node<v_1975,flted_143_1973>@M[Orig][] * 
                              res::sll2<flted_143_1972,sres_1976,lres_1974>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lres_1974<=xl & xs<=xl & v_1975<=sres_1976 & 
                                 xs<=sres_1976 & sres_1976<=lres_1974 & 
                                 xs<=v_1975]
                               [x'!=null]
                               [0<=flted_143_1972 & 0<=n & 1+flted_143_1972=n]
                               [null=flted_143_1973]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qmin_1959:sres<=lres & lres<=xl & xs<=qmin_1959 & 
  qmin_1959<=sres)) --> GN(sres,xs,lres,xl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1]
!!! REL :  GNN(sm1,lg1,sm2,lg2)
!!! POST:  sm2>=sm1 & lg2>=sm2 & lg1>=lg2
!!! PRE :  sm1<=lg1
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[n; sm1; 
                    lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                    (([null!=x][0<=n & 0!=n][sm1<=lg1]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_206_102,sm2,
                                lg2: res::sll2<flted_206_102,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_206_102 & 2+flted_206_102=n]
                                 [sm2<=lg2 & GNN(sm1,lg1,sm2,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; 
                  lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(
                          ([MayLoop][sm1<=lg1 & 2<=n | n<=0 & sm1<=lg1]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_206_2042,sm2_2043,
                              lg2_2044: res::sll2<flted_206_2042,sm2_2043,lg2_2044>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lg2_2044<=lg1 & sm1<=lg1 & sm1<=sm2_2043 & 
                                 sm2_2043<=lg2_2044]
                               [0<=flted_206_2042 & 0<=n & 2+flted_206_2042=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qs_1999:sm2<=lg2 & 
  exists(qmin_2001:exists(qmin_2034:exists(ql_2000:qs_1999<=qmin_2034 & 
  qmin_2001<=qs_1999 & sm1<=qmin_2001 & qmin_2034<=sm2 & lg2<=ql_2000 & 
  ql_2000<=lg1))))) --> GNN(sm1,lg1,sm2,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(sres,xs,lres,xl)
!!! POST:  sres>=xs & lres>=sres & xl>=lres
!!! PRE :  xs<=xl
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_186_106,sres,
                                lres: res::sll2<flted_186_106,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_186_106 & 1+flted_186_106=n]
                                 [sres<=lres & GT(sres,xs,lres,xl)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][xs<=xl]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(flted_186_2077,sres_2078,
                              lres_2079: res::sll2<flted_186_2077,sres_2078,lres_2079>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lres_2079<=xl & xs<=xl & xs<=sres_2078 & 
                                 sres_2078<=lres_2079]
                               [0<=flted_186_2077 & 0<=n & 1+flted_186_2077=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sres<=lres & lres<=xl & exists(qmin_2069:xs<=qmin_2069 & 
  qmin_2069<=sres)) --> GT(sres,xs,lres,xl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
!!! REL :  FIL(xs,xl,sres,lres)
!!! POST:  lres>=sres & xl>=xs
!!! PRE :  xs<=xl
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([0<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 80::
                                EXISTS(nres,sres,
                                lres: res::sll2<nres,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=nres & nres<=n]
                                 [sres<=lres & FIL(xs,xl,sres,lres)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([0<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][xs<=xl]))&{FLOW,(1,23)=__flow}
                            EAssume 80::
                              EXISTS(nres_2709,sres_2710,
                              lres_2711: res::sll2<nres_2709,sres_2710,lres_2711>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([xs<=xl][sres_2710<=lres_2711]
                               [0<=nres_2709 & 0<=n & nres_2709<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs_2611<=xl_2612 & sres_2672=sres & lres_2673=lres & xl_2612<=xl & 
  sres<=lres & FIL(xs_2611,xl_2612,sres_2672,lres_2673) & 
  exists(qmin_2592:qmin_2592<=xs_2611 & 
  xs<=qmin_2592)) --> FIL(xs,xl,sres,lres),
 (exists(v:exists(qmin_2592:FIL(xs_2633,xl_2634,sres_2659,lres_2660) & 
  lres_2660<=lres & xl_2634<=xl & xs_2633<=xl_2634 & sres_2659<=lres_2660 & 
  ((1+v)<=qmin_2592 | (1+qmin_2592)<=v) & xs<=qmin_2592 & sres<=qmin_2592 & 
  qmin_2592<=xs_2633 & qmin_2592<=sres_2659))) --> FIL(xs,xl,sres,lres),
 (sres<=lres & xs<=xl) --> FIL(xs,xl,sres,lres)]
!!! NEW ASSUME:[ RELASS [FIL]: ( FIL(xs_2633,xl_2634,sres_2659,lres_2660)) -->  xl_2634<xs_2633 | xs_2633<=xl_2634 & xs_2633<=sres_2659 | 
lres_2660<sres_2659 & sres_2659<xs_2633 & xs_2633<=xl_2634]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(sm1,sm2,lg1,lg2)
!!! POST:  sm2>=sm1 & lg2>=sm2 & lg1>=lg2
!!! PRE :  sm1<=lg1
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; sm1; 
                    lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                    (([null!=x][0<=m & 0!=m][sm1<=lg1]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_104_118,sm2,
                                lg2: x'::sll2<flted_104_118,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_104_118 & 1+flted_104_118=m]
                                 [sm2<=lg2 & PF(sm1,sm2,lg1,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; sm1; 
                  lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=m][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][sm1<=lg1]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(flted_104_3011,sm2_3012,
                              lg2_3013: x'::sll2<flted_104_3011,sm2_3012,lg2_3013>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lg2_3013<=lg1 & sm1<=lg1 & sm1<=sm2_3012 & 
                                 sm2_3012<=lg2_3013]
                               [0<=flted_104_3011 & 0<=m & 1+flted_104_3011=m]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm2<=lg2 & lg2<=lg1 & exists(qmin_2998:sm1<=qmin_2998 & 
  qmin_2998<=sm2)) --> PF(sm1,sm2,lg1,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[n; sm; 
                    lg](ex)x::sll2<n,sm,lg>@M[Orig][LHSCase]@ rem br[{384,383}]&
                    (([sm<=lg & PUF(v,sm)][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(v_122,flted_93_121,
                                lg1: x'::sll2<flted_93_121,v_122,lg1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_93_121 & -1+flted_93_121=n]
                                 [v=v_122 & v_122<=lg1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; 
                  lg](ex)x::sll2<n,sm,lg>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([sm<=lg & PUF(v,sm)][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              EXISTS(v_3043,flted_93_3044,
                              lg1_3045: x'::sll2<flted_93_3044,v_3043,lg1_3045>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([1+n=flted_93_3044 & 0<=n & 0<=flted_93_3044]
                               [v=v_3043 & v<=lg1_3045][sm<=lg]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[ RELASS [PUF]: ( PUF(v,sm)) -->  v<=sm]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! REL :  SNULL(xs,v,sl_3117)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [x]
                                EXISTS(flted_196_104,v,
                                sl: x'::node<v,flted_196_104>@M[Orig][]&(
                                ([null=flted_196_104][SNULL(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [x]
                              EXISTS(flted_196_3118,
                              v_3119: x'::node<v_3119,flted_196_3118>@M[Orig][]&
                              (
                              ([x'!=null][null=flted_196_3118][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(xl:exists(ql_3113:ql_3113<=xl & xs<=v & 
  exists(qs_3112:qs_3112<=ql_3113 & v<=qs_3112)))) --> SNULL(xs,v,sl_3117)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! REL :  SNULL2(xs,v,sl_3160)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL2]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(flted_173_108,v,
                                sl: x'::node<v,flted_173_108>@M[Orig][]&(
                                ([null=flted_173_108][SNULL2(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              EXISTS(flted_173_3161,
                              v_3162: x'::node<v_3162,flted_173_3161>@M[Orig][]&
                              (
                              ([x'!=null][null=flted_173_3161][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(xl:exists(ql_3152:ql_3152<=xl & xs<=v & 
  exists(qs_3151:qs_3151<=ql_3152 & v<=qs_3151)))) --> SNULL2(xs,v,sl_3160)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
!!! REL :  SPLIT(sm,sl,sm1,sl1,sm2,sl2)
!!! POST:  sm2>=sm & sm2>=sm1 & sl2>=sm2 & sl>=sl2 & sl1>=sm & sl1>=sm1
!!! PRE :  sm<=sl
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; sm; 
                    sl](ex)x::sll2<n,sm,sl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([(1+a)<=n & 1<=a][sm<=sl][null!=x]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 67::ref [x]
                                EXISTS(n2,n1,sm1,sl1,sm2,
                                sl2: x'::sll2<n1,sm1,sl1>@M[Orig][LHSCase]@ rem br[{383}] * 
                                res::sll2<n2,sm2,sl2>@M[Orig][LHSCase]@ rem br[{383}]&
                                (
                                ([a=n1 & 0!=n1 & 0!=n2 & 0<=n1 & 0<=n2 & 
                                   n=n1+n2]
                                 [sm1<=sl1 & sm2<=sl2 & 
                                   SPLIT(sm,sl,sm1,sl1,sm2,sl2)]
                                 [null!=x'][null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; 
                  sl](ex)x::sll2<n,sm,sl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][sm<=sl][1<=a & (1+a)<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][sm<=sl]))&{FLOW,(1,23)=__flow}
                            EAssume 67::ref [x]
                              EXISTS(n2_3396,n1_3397,sm1_3398,sl1_3399,
                              sm2_3400,
                              sl2_3401: x'::sll2<n1_3397,sm1_3398,sl1_3399>@M[Orig][LHSCase]@ rem br[{383}] * 
                              res::sll2<n2_3396,sm2_3400,sl2_3401>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([sm1_3398<=sl1_3399 & sm<=sl & sm<=sl1_3399 & 
                                 sm2_3400<=sl2_3401 & sm<=sm2_3400 & 
                                 sm1_3398<=sm2_3400 & sl2_3401<=sl]
                               [null!=res][null!=x']
                               [a=n1_3397 & 0!=n1_3397 & 0<=n & n=n1_3397+
                                 n2_3396 & 0!=n2_3396 & 0<=n1_3397 & 
                                 0<=n2_3396]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qmin_3260:sm2<=sl2 & sl2<=sl & sm1<=qmin_3260 & sm<=qmin_3260 & 
  qmin_3260<=sm2 & qmin_3260<=sl1)) --> SPLIT(sm,sl,sm1,sl1,sm2,sl2),
 (exists(qmin_3366:sm1_3360<=sl1_3361 & sm_3302<=sl_3303 & sm2_3362=sm2 & 
  sl2_3363=sl2 & sl_3303<=sl & sl1_3361<=sl1 & sm2<=sl2 & 
  SPLIT(sm_3302,sl_3303,sm1_3360,sl1_3361,sm2_3362,sl2_3363) & 
  qmin_3366<=sm1_3360 & qmin_3366<=sm_3302 & sm1<=qmin_3366 & 
  sm<=qmin_3366)) --> SPLIT(sm,sl,sm1,sl1,sm2,sl2)]
!!! NEW ASSUME:[ RELASS [SPLIT]: ( SPLIT(sm_3302,sl_3303,sm1_3360,sl1_3361,sm2_3362,sl2_3363)) -->  sl_3303<sm_3302 | sm_3302<=sl_3303 & sm_3302<=sm1_3360 | 
sl1_3361<sm1_3360 & sm1_3360<sm_3302 & sm_3302<=sl_3303]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1593 invocations 
16 false contexts at: ( (178,13)  (178,4)  (35,17)  (35,24)  (36,7)  (36,14)  (307,4)  (307,11)  (312,4)  (312,11)  (311,10)  (311,4)  (310,9)  (310,13)  (310,4)  (310,4) )

Total verification time: 2.38 second(s)
	Time spent in main process: 1.91 second(s)
	Time spent in child processes: 0.47 second(s)
