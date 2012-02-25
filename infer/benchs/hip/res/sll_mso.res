
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
                                                       res::sll2<n_93,sm,lg>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                                       (
                                                       ([sm<=lg & sm<=v & 
                                                          v<=lg]
                                                        [n_93=n & 0<=n_93 & 
                                                          1<=n]
                                                        ))&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           n<0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 62::
                                                       true&(([n<=-1]))&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (sm<=v & v<=lg) --> CL(sm,lg,v),
 (sm_1340<=lg_1341 & sm<=v & v<=sm_1340 & lg_1341<=lg & 
  CL(sm_1340,lg_1341,v)) --> CL(sm,lg,v)]
!!! NEW ASSUME:[ RELASS [CL]: ( CL(sm_1340,lg_1341,v)) -->  lg_1341<sm_1340 | v<=sm_1340 & sm_1340<=lg_1341]
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
                                EXISTS(flted_135_112,flted_135_113,lres,v,
                                sres: x'::node<v,flted_135_113>@M[Orig][] * 
                                res::sll2<flted_135_112,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_135_113]
                                 [0<=flted_135_112 & 1+flted_135_112=n]
                                 [sres<=lres & v<=sres & xs<=v & 
                                   GN(sres,xs,lres,xl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][xs<=xl]))&{FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              x'::node<v,flted_135_113>@M[Orig][] * 
                              res::sll2<flted_135_112,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lres<=xl & xs<=xl & v<=sres & xs<=sres & 
                                 sres<=lres & xs<=v]
                               [x'!=null]
                               [0<=flted_135_112 & 0<=n & 1+flted_135_112=n]
                               [flted_135_113=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(qmin_1950:sres<=lres & lres<=xl & xs<=qmin_1950 & 
  qmin_1950<=sres)) --> GN(sres,xs,lres,xl)]
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
                                EXISTS(flted_200_102,sm2,
                                lg2: res::sll2<flted_200_102,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_200_102 & 2+flted_200_102=n]
                                 [sm2<=lg2 & GNN(sm1,lg1,sm2,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; 
                  lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(
                          ([MayLoop][sm1<=lg1 & 2<=n | n<=0 & sm1<=lg1]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 38::
                              res::sll2<flted_200_102,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lg2<=lg1 & sm1<=lg1 & sm1<=sm2 & sm2<=lg2]
                               [0<=flted_200_102 & 0<=n & 2+flted_200_102=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(qs_1985:sm2<=lg2 & 
  exists(qmin_1987:exists(qmin_2020:exists(ql_1986:qs_1985<=qmin_2020 & 
  qmin_1987<=qs_1985 & sm1<=qmin_1987 & qmin_2020<=sm2 & lg2<=ql_1986 & 
  ql_1986<=lg1))))) --> GNN(sm1,lg1,sm2,lg2)]
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
                                EXISTS(flted_179_106,sres,
                                lres: res::sll2<flted_179_106,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_179_106 & 1+flted_179_106=n]
                                 [sres<=lres & GT(sres,xs,lres,xl)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][xs<=xl]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              res::sll2<flted_179_106,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lres<=xl & xs<=xl & xs<=sres & sres<=lres]
                               [0<=flted_179_106 & 0<=n & 1+flted_179_106=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (sres<=lres & lres<=xl & exists(qmin_2052:xs<=qmin_2052 & 
  qmin_2052<=sres)) --> GT(sres,xs,lres,xl)]
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
                              EAssume 73::
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
                            EAssume 73::
                              res::sll2<nres,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([xs<=xl][sres<=lres][0<=nres & 0<=n & nres<=n]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v:exists(qmin_2572:FIL(xs_2599,xl_2600,sres_2625,lres_2626) & 
  lres_2626<=lres & xl_2600<=xl & xs_2599<=xl_2600 & sres_2625<=lres_2626 & 
  ((1+v)<=qmin_2572 | (1+qmin_2572)<=v) & xs<=qmin_2572 & sres<=qmin_2572 & 
  qmin_2572<=xs_2599 & qmin_2572<=sres_2625))) --> FIL(xs,xl,sres,lres),
 (sres<=lres & xs<=xl) --> FIL(xs,xl,sres,lres)]
!!! NEW ASSUME:[ RELASS [FIL]: ( FIL(xs_2599,xl_2600,sres_2625,lres_2626)) -->  xl_2600<xs_2599 | xs_2599<=xl_2600 & xs_2599<=sres_2625 | 
lres_2626<sres_2625 & sres_2625<xs_2599 & xs_2599<=xl_2600]
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
                                EXISTS(flted_94_118,sm2,
                                lg2: x'::sll2<flted_94_118,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_94_118 & 1+flted_94_118=m]
                                 [sm2<=lg2 & PF(sm1,sm2,lg1,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; sm1; 
                  lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=m][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][sm1<=lg1]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::sll2<flted_94_118,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lg2<=lg1 & sm1<=lg1 & sm1<=sm2 & sm2<=lg2]
                               [0<=flted_94_118 & 0<=m & 1+flted_94_118=m]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (sm2<=lg2 & lg2<=lg1 & exists(qmin_2946:sm1<=qmin_2946 & 
  qmin_2946<=sm2)) --> PF(sm1,sm2,lg1,lg2)]
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
                                EXISTS(v_122,flted_82_121,
                                lg1: x'::sll2<flted_82_121,v_122,lg1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_82_121 & -1+flted_82_121=n]
                                 [v=v_122 & v_122<=lg1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm; 
                  lg](ex)x::sll2<n,sm,lg>@M[Orig][LHSCase]@ rem br[{384,383}]&
                  (([sm<=lg & PUF(v,sm)][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              x'::sll2<flted_82_121,v_122,lg1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([0<=flted_82_121 & 0<=n & -1+flted_82_121=n]
                               [v=v_122 & v_122<=lg1][sm<=lg]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[ RELASS [PUF]: ( PUF(v,sm)) -->  v<=sm]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! REL :  SNULL(xs,v,sl_3059)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [x]
                                EXISTS(flted_189_104,v,
                                sl: x'::node<v,flted_189_104>@M[Orig][]&(
                                ([null=flted_189_104][SNULL(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [x]
                              x'::node<v,flted_189_104>@M[Orig][]&(
                              ([x'!=null][flted_189_104=null][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(xl:exists(ql_3055:ql_3055<=xl & xs<=v & 
  exists(qs_3054:qs_3054<=ql_3055 & v<=qs_3054)))) --> SNULL(xs,v,sl_3059)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! REL :  SNULL2(xs,v,sl_3099)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL2]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(flted_166_108,v,
                                sl: x'::node<v,flted_166_108>@M[Orig][]&(
                                ([null=flted_166_108][SNULL2(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              x'::node<v,flted_166_108>@M[Orig][]&(
                              ([x'!=null][flted_166_108=null][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(xl:exists(ql_3091:ql_3091<=xl & xs<=v & 
  exists(qs_3090:qs_3090<=ql_3091 & v<=qs_3090)))) --> SNULL2(xs,v,sl_3099)]
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
                              EAssume 84::ref [x]
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
                            EAssume 84::ref [x]
                              x'::sll2<n1,sm1,sl1>@M[Orig][LHSCase]@ rem br[{383}] * 
                              res::sll2<n2,sm2,sl2>@M[Orig][LHSCase]@ rem br[{383}]&
                              (
                              ([sm1<=sl1 & sm<=sl & sm<=sl1 & sm2<=sl2 & 
                                 sm<=sm2 & sm1<=sm2 & sl2<=sl]
                               [null!=res][null!=x']
                               [n1=a & 0!=n1 & 0<=n & n=n1+n2 & 0!=n2 & 
                                 0<=n1 & 0<=n2]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(qmin_3196:sm2<=sl2 & sl2<=sl & sm1<=qmin_3196 & sm<=qmin_3196 & 
  qmin_3196<=sm2 & qmin_3196<=sl1)) --> SPLIT(sm,sl,sm1,sl1,sm2,sl2),
 (exists(qmin_3302:sm1_3296<=sl1_3297 & sm_3238<=sl_3239 & sm2_3298=sm2 & 
  sl2_3299=sl2 & sl_3239<=sl & sl1_3297<=sl1 & sm2<=sl2 & 
  SPLIT(sm_3238,sl_3239,sm1_3296,sl1_3297,sm2_3298,sl2_3299) & 
  qmin_3302<=sm1_3296 & qmin_3302<=sm_3238 & sm1<=qmin_3302 & 
  sm<=qmin_3302)) --> SPLIT(sm,sl,sm1,sl1,sm2,sl2)]
!!! NEW ASSUME:[ RELASS [SPLIT]: ( SPLIT(sm_3238,sl_3239,sm1_3296,sl1_3297,sm2_3298,sl2_3299)) -->  sl_3239<sm_3238 | sm_3238<=sl_3239 & sm_3238<=sm1_3296 | 
sl1_3297<sm1_3296 & sm1_3296<sm_3238 & sm_3238<=sl_3239]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1536 invocations 
20 false contexts at: ( (171,13)  (171,4)  (362,10)  (362,6)  (361,10)  (361,6)  (35,17)  (35,24)  (36,7)  (36,14)  (303,4)  (303,11)  (308,4)  (308,11)  (307,10)  (307,4)  (306,9)  (306,13)  (306,4)  (306,4) )

Total verification time: 2.34 second(s)
	Time spent in main process: 1.88 second(s)
	Time spent in child processes: 0.46 second(s)
