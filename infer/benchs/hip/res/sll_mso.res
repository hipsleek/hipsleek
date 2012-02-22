
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
!!! NEW RELS:[ (exists(qmin_1953:sres<=lres & lres<=xl & xs<=qmin_1953 & 
  qmin_1953<=sres)) --> GN(sres,xs,lres,xl)]
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
!!! NEW RELS:[ (exists(qs_1989:sm2<=lg2 & 
  exists(qmin_1991:exists(qmin_2024:exists(ql_1990:qs_1989<=qmin_2024 & 
  qmin_1991<=qs_1989 & sm1<=qmin_1991 & qmin_2024<=sm2 & lg2<=ql_1990 & 
  ql_1990<=lg1))))) --> GNN(sm1,lg1,sm2,lg2)]
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
!!! NEW RELS:[ (sres<=lres & lres<=xl & exists(qmin_2057:xs<=qmin_2057 & 
  qmin_2057<=sres)) --> GT(sres,xs,lres,xl)]
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
                              ([sres<=lres & xs<=xl & FIL(xs,xl,sres,lres)]
                               [0<=nres & 0<=n & nres<=n]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v:exists(qmin_2578:FIL(xs_2605,xl_2606,sres_2631,lres_2632) & 
  lres_2632<=lres & xl_2606<=xl & xs_2605<=xl_2606 & sres_2631<=lres_2632 & 
  ((1+v)<=qmin_2578 | (1+qmin_2578)<=v) & xs<=qmin_2578 & sres<=qmin_2578 & 
  qmin_2578<=xs_2605 & qmin_2578<=sres_2631))) --> FIL(xs,xl,sres,lres),
 (sres<=lres & xs<=xl) --> FIL(xs,xl,sres,lres)]
!!! NEW ASSUME:[ RELASS [FIL]: ( FIL(xs_2605,xl_2606,sres_2631,lres_2632)) -->  xl_2606<xs_2605 | xs_2605<=xl_2606 & xs_2605<=sres_2631 | 
lres_2632<sres_2631 & sres_2631<xs_2605 & xs_2605<=xl_2606]
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
!!! NEW RELS:[ (sm2<=lg2 & lg2<=lg1 & exists(qmin_2952:sm1<=qmin_2952 & 
  qmin_2952<=sm2)) --> PF(sm1,sm2,lg1,lg2)]
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
                  (([0<=n][sm<=lg & PUF(v,sm)]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              x'::sll2<flted_82_121,v_122,lg1>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([v_122=v & v<=sm & lg<=lg1 & sm<=lg & 
                                 PUF(v,sm)]
                               [-1+flted_82_121=n & 0<=n][x'!=null]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[ RELASS [PUF]: ( PUF(v,sm)) -->  v<=sm]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! REL :  SNULL(xs,v,sl_3065)
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
!!! NEW RELS:[ (exists(xl:exists(ql_3061:ql_3061<=xl & xs<=v & 
  exists(qs_3060:qs_3060<=ql_3061 & v<=qs_3060)))) --> SNULL(xs,v,sl_3065)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! REL :  SNULL2(xs,v,sl_3107)
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
!!! NEW RELS:[ (exists(xl:exists(ql_3099:ql_3099<=xl & xs<=v & 
  exists(qs_3098:qs_3098<=ql_3099 & v<=qs_3098)))) --> SNULL2(xs,v,sl_3107)]
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
!!! NEW RELS:[ (exists(qmin_3206:sm2<=sl2 & sl2<=sl & sm1<=qmin_3206 & sm<=qmin_3206 & 
  qmin_3206<=sm2 & qmin_3206<=sl1)) --> SPLIT(sm,sl,sm1,sl1,sm2,sl2),
 (exists(qmin_3312:sm1_3306<=sl1_3307 & sm_3248<=sl_3249 & sm2_3308=sm2 & 
  sl2_3309=sl2 & sl_3249<=sl & sl1_3307<=sl1 & sm2<=sl2 & 
  SPLIT(sm_3248,sl_3249,sm1_3306,sl1_3307,sm2_3308,sl2_3309) & 
  qmin_3312<=sm1_3306 & qmin_3312<=sm_3248 & sm1<=qmin_3312 & 
  sm<=qmin_3312)) --> SPLIT(sm,sl,sm1,sl1,sm2,sl2)]
!!! NEW ASSUME:[ RELASS [SPLIT]: ( SPLIT(sm_3248,sl_3249,sm1_3306,sl1_3307,sm2_3308,sl2_3309)) -->  sl_3249<sm_3248 | sm_3248<=sl_3249 & sm_3248<=sm1_3306 | 
sl1_3307<sm1_3306 & sm1_3306<sm_3248 & sm_3248<=sl_3249]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1674 invocations 
20 false contexts at: ( (171,13)  (171,4)  (362,10)  (362,6)  (361,10)  (361,6)  (35,17)  (35,24)  (36,7)  (36,14)  (303,4)  (303,11)  (308,4)  (308,11)  (307,10)  (307,4)  (306,9)  (306,13)  (306,4)  (306,4) )

Total verification time: 3.47 second(s)
	Time spent in main process: 2.56 second(s)
	Time spent in child processes: 0.91 second(s)
