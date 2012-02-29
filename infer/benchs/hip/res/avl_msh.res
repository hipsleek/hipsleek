
Processing file "avl_msh.ss"
Parsing avl_msh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure build_avl1$node~node... 
!!! OLD SPECS: ((None,[]),EInfer [x,y,res]
              EBase exists (Expl)(Impl)[mx; my; 
                    nx1](ex)EXISTS(nx1_88: x::avl<mx,nx1>@M[Orig][LHSCase]@ rem br[{650}] * 
                    y::avl<my,nx1_88>@M[Orig][LHSCase]@ rem br[{650}]&(
                    ([null!=x][nx1=nx1_88 & 0!=nx1_88 & 0<=nx1]
                     [0<=mx & 0!=mx][0<=my & 0!=my][null!=y]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                EXISTS(flted_127_87,
                                k: res::avl<flted_127_87,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_127_87 & flted_127_87=1+mx+my]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[mx; my; 
                  nx1](ex)x::avl<mx,nx1>@M[Orig][LHSCase]@ rem br[{650}] * 
                  y::avl<my,nx1_88>@M[Orig][LHSCase]@ rem br[{650}]&(
                  ([x!=null][nx1=nx1_88 & 1<=nx1][1<=mx][1<=my][y!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              EXISTS(flted_127_1689,
                              k_1690: res::avl<flted_127_1689,k_1690>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([y!=null][res!=null]
                               [-1+k_1690=nx1 & 0<=nx1 & 1<=nx1][x!=null]
                               [flted_127_1689=1+mx+my & 0<=mx & 1<=mx & 
                                 0<=my & 1<=my]
                               [0<=nx1_88]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl1$node~node SUCCESS

Checking procedure build_avl2$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [x,y,z]
              EBase exists (Expl)(Impl)[my; mz; ny; Anon_12; Anon_13; 
                    Anon_14; 
                    Anon_15](ex)EXISTS(ny_84: y::avl<my,ny>@M[Orig][LHSCase]@ rem br[{650}] * 
                    z::avl<mz,ny_84>@M[Orig][LHSCase]@ rem br[{650}] * 
                    x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                    ([null!=y][ny=ny_84 & 0!=ny_84 & 0<=ny][0<=my & 0!=my]
                     [0<=mz & 0!=mz][null!=z][x!=null]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 46::ref [x]
                                EXISTS(flted_141_83,
                                k: x'::avl<flted_141_83,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_141_83 & flted_141_83=1+my+mz]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[my; mz; ny; Anon_12; Anon_13; Anon_14; 
                  Anon_15](ex)y::avl<my,ny>@M[Orig][LHSCase]@ rem br[{650}] * 
                  z::avl<mz,ny_84>@M[Orig][LHSCase]@ rem br[{650}] * 
                  x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                  ([y!=null][ny=ny_84 & 1<=ny][1<=my][1<=mz][z!=null]
                   [x!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 46::ref [x]
                              EXISTS(flted_141_1805,
                              k_1806: x'::avl<flted_141_1805,k_1806>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([1+ny=k_1806 & 0<=ny & 2<=k_1806]
                               [x'=x & x'!=null][z!=null][y!=null]
                               [flted_141_1805=1+my+mz & 0<=my & 1<=mz & 
                                 0<=mz & 1<=my]
                               [0<=ny_84]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl2$node~node~node SUCCESS

Checking procedure get_max$int~int... 
Procedure get_max$int~int SUCCESS

Checking procedure height$node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[m; 
                    n](ex)x::avl<m,n>@I[Orig][LHSCase]@ rem br[{651,650}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  n](ex)x::avl<m,n>@I[Orig][LHSCase]@ rem br[{651,650}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(
                              ([null=x][0=m & 0<=m][0=n & 0<=n][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1859,n_1860,p_1861,m1_1862,
                                 n1_1863,q_1864,m2_1865,
                                 n2_1866: x::node<Anon_1859,n_1860,p_1861,q_1864>@I[Orig][] * 
                                 p_1861::avl<m1_1862,n1_1863>@I[Orig]@ rem br[{651,650}] * 
                                 q_1864::avl<m2_1865,n2_1866>@I[Orig]@ rem br[{651,650}]&
                                 (
                                 ([(n1_1863=res-1 & n=res & m=m2_1865+
                                    m1_1862+1 & n_1860=res & (res-
                                    2)<=n2_1866 & 0<=n2_1866 & n2_1866<res & 
                                    0<=m1_1862 & 0<=m2_1865 & x!=null | 
                                    n2_1866=res-1 & n1_1863=res-2 & n=res & 
                                    m=m2_1865+m1_1862+1 & n_1860=res & 
                                    0<=m1_1862 & 0<=m2_1865 & 2<=res & 
                                    x!=null) & 0<=m & 0<=n]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d,res]
              EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                    an](ex)EXISTS(an_99: a::avl<am,an>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    d::avl<dm,an_99>@M[Orig][LHSCase]@ rem br[{651,650}]&(
                    ([an=an_99 & an=max(bn,cn) & 0<=bn & 0<=an & 0<=cn & (-1+
                       bn)<=cn & (-1+cn)<=bn]
                     [0<=am][0<=bm][0<=cm][0<=dm]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::
                                EXISTS(flted_81_98,
                                k: res::avl<flted_81_98,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_81_98 & flted_81_98=3+am+bm+cm+dm]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                  an](ex)a::avl<am,an>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  d::avl<dm,an_99>@M[Orig][LHSCase]@ rem br[{651,650}]&(
                  ([0<=am][0<=bm][0<=cm][0<=dm]
                   [an=an_99 & bn<=an & (2*an)<=(1+bn+cn) & cn<=an & an<=(bn+
                     cn)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::
                              EXISTS(flted_81_2032,
                              k_2033: res::avl<flted_81_2032,k_2033>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([(cn=k_2033-2 & bn=k_2033-2 & an=k_2033-2 & 
                                 cm=(((flted_81_2032-dm)-bm)-am)-3 & 0<=dm & 
                                 2<=k_2033 & res!=null & 0<=bm & 0<=am & (3+
                                 dm+bm+am)<=flted_81_2032 | cn=k_2033-2 & 
                                 bn=k_2033-3 & an=k_2033-2 & 
                                 cm=(((flted_81_2032-dm)-bm)-am)-3 & 0<=dm & 
                                 3<=k_2033 & res!=null & 0<=bm & 0<=am & (3+
                                 dm+bm+am)<=flted_81_2032 | cn=k_2033-3 & 
                                 bn=k_2033-2 & an=k_2033-2 & 
                                 cm=(((flted_81_2032-dm)-bm)-am)-3 & 0<=dm & 
                                 3<=k_2033 & res!=null & 0<=bm & 0<=am & (3+
                                 dm+bm+am)<=flted_81_2032) & 0<=dm & 0<=an & 
                                 0<=cm & 0<=am & 0<=cn & 0<=bn & 0<=bm]
                               [0<=an_99]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_left$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_double_right$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d,res]
              EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                    an](ex)EXISTS(an_93: a::avl<am,an>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    d::avl<dm,an_93>@M[Orig][LHSCase]@ rem br[{651,650}]&(
                    ([an=an_93 & an=max(bn,cn) & 0<=bn & 0<=an & 0<=cn & (-1+
                       cn)<=bn & (-1+bn)<=cn]
                     [0<=am][0<=bm][0<=cm][0<=dm]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                EXISTS(flted_104_92,
                                k: res::avl<flted_104_92,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_104_92 & flted_104_92=3+am+bm+cm+
                                   dm]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                  an](ex)a::avl<am,an>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  d::avl<dm,an_93>@M[Orig][LHSCase]@ rem br[{651,650}]&(
                  ([0<=am][0<=bm][0<=cm][0<=dm]
                   [an=an_93 & bn<=an & (2*an)<=(1+bn+cn) & cn<=an & an<=(bn+
                     cn)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              EXISTS(flted_104_2199,
                              k_2200: res::avl<flted_104_2199,k_2200>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([(cn=k_2200-2 & bn=k_2200-2 & an=k_2200-2 & 
                                 cm=(((flted_104_2199-dm)-bm)-am)-3 & 
                                 0<=dm & 2<=k_2200 & res!=null & 0<=bm & 
                                 0<=am & (3+dm+bm+am)<=flted_104_2199 | 
                                 cn=k_2200-2 & bn=k_2200-3 & an=k_2200-2 & 
                                 cm=(((flted_104_2199-dm)-bm)-am)-3 & 
                                 0<=dm & 3<=k_2200 & res!=null & 0<=bm & 
                                 0<=am & (3+dm+bm+am)<=flted_104_2199 | 
                                 cn=k_2200-3 & bn=k_2200-2 & an=k_2200-2 & 
                                 cm=(((flted_104_2199-dm)-bm)-am)-3 & 
                                 0<=dm & 3<=k_2200 & res!=null & 0<=bm & 
                                 0<=am & (3+dm+bm+am)<=flted_104_2199) & 
                                 0<=dm & 0<=an & 0<=cm & 0<=am & 0<=cn & 
                                 0<=bn & 0<=bm]
                               [0<=an_93]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_right$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_left$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [l,rl,rr,res]
              EBase exists (Expl)(Impl)[lm; rlm; ln; rrm](ex)EXISTS(ln_116,
                    flted_36_115: l::avl<lm,ln>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    rl::avl<rlm,ln_116>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    rr::avl<rrm,flted_36_115>@M[Orig][LHSCase]@ rem br[{650}]&
                    (
                    ([ln=ln_116 & 0<=ln & -1+flted_36_115=ln][0<=lm][
                     0<=rlm][0<=rrm & 0!=rrm][null!=rr]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(flted_37_114,
                                k: res::avl<flted_37_114,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_37_114 & flted_37_114=2+lm+rlm+rrm]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[lm; rlm; ln; 
                  rrm](ex)l::avl<lm,ln>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  rl::avl<rlm,ln_116>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  rr::avl<rrm,flted_36_115>@M[Orig][LHSCase]@ rem br[{650}]&(
                  ([1+ln=flted_36_115 & 1<=flted_36_115 & 1+
                     ln_116=flted_36_115]
                   [0<=lm][0<=rlm][1<=rrm][rr!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              EXISTS(flted_37_2270,
                              k_2271: res::avl<flted_37_2270,k_2271>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([flted_37_2270=2+lm+rlm+rrm & 0<=lm & 
                                 0<=rlm & 0<=rrm & 1<=rrm]
                               [rr!=null][-2+k_2271=ln & 0<=ln][res!=null]
                               [0<=flted_36_115][0<=ln_116]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_left$node~node~node SUCCESS

Checking procedure rotate_right$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [ll,lr,r,res]
              EBase exists (Expl)(Impl)[llm; lln; lrm; 
                    rm](ex)EXISTS(flted_53_107,
                    flted_53_108: ll::avl<llm,lln>@M[Orig][LHSCase]@ rem br[{650}] * 
                    lr::avl<lrm,flted_53_108>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                    r::avl<rm,flted_53_107>@M[Orig][LHSCase]@ rem br[{651,650}]&
                    (
                    ([0<=flted_53_108 & 1+flted_53_107=lln & 1+
                       flted_53_108=lln]
                     [0!=llm & 0<=llm][0<=lrm][0<=rm][null!=ll]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 10::
                                EXISTS(flted_54_106,
                                k: res::avl<flted_54_106,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_54_106 & flted_54_106=2+llm+lrm+rm]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[llm; lln; lrm; 
                  rm](ex)ll::avl<llm,lln>@M[Orig][LHSCase]@ rem br[{650}] * 
                  lr::avl<lrm,flted_53_108>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  r::avl<rm,flted_53_107>@M[Orig][LHSCase]@ rem br[{651,650}]&
                  (
                  ([flted_53_107=flted_53_108 & -1+lln=flted_53_107 & 
                     0<=flted_53_107]
                   [1<=llm][0<=lrm][0<=rm][ll!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 10::
                              EXISTS(flted_54_2343,
                              k_2344: res::avl<flted_54_2343,k_2344>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([2+llm+lrm+rm=flted_54_2343 & 0<=llm & (3+lrm+
                                 rm)<=flted_54_2343 & 0<=rm & 0<=lrm]
                               [ll!=null][-1+k_2344=lln & 0<=lln & 1<=lln]
                               [res!=null][0<=flted_53_107][0<=flted_53_108]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_right$node~node~node SUCCESS

Checking procedure insert$node~int... 
Procedure Call:avl_msh.ss:179: 25: 
Verification Context:(Line:162,Col:10)
Proving precondition in method rotate_right$node~node~node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[llm; lln; lrm; 
                  rm](ex)v_node_179_1095'::avl<llm,lln>@M[Orig][LHSCase]@ rem br[{650}] * 
                  v_node_179_1094'::avl<lrm,flted_53_108>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  v_node_179_1093'::avl<rm,flted_53_107>@M[Orig][LHSCase]@ rem br[{651,650}]&
                  (
                  ([flted_53_107=flted_53_108 & -1+lln=flted_53_107 & 
                     0<=flted_53_107]
                   [1<=llm][0<=lrm][0<=rm][v_node_179_1095'!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 10::
                              EXISTS(flted_54_2343,
                              k_2344: res::avl<flted_54_2343,k_2344>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([2+llm+lrm+rm=flted_54_2343 & 0<=llm & (3+lrm+
                                 rm)<=flted_54_2343 & 0<=rm & 0<=lrm]
                               [v_node_179_1095'!=null]
                               [-1+k_2344=lln & 0<=lln & 1<=lln][res!=null]
                               [0<=flted_53_107][0<=flted_53_108]))&
                              {FLOW,(20,21)=__norm}))
Current States: [ or[x'::node<Anon_2383,n_2382,v_node_173_2429,q_2387>@M[Orig][] * v_node_173_2429::node<Anon_2474,n_2475,p_2476,q_2479>@I[Orig][] * p_2476::node<Anon_2633,n_2634,p_2635,q_2638>@I[Orig][] * p_2635::avl<m1_2636,n1_2637>@I[Orig]@ rem br[{651,650}] * q_2638::avl<m2_2639,n2_2640>@I[Orig]@ rem br[{651,650}]&(([
                                                                    v_bool_177_1172']
                                                                    [n2_2389=n_2485 & 
                                                                    n2_2389=m_2484 & 
                                                                    n2_2389=m2_2388 & 
                                                                    n2_2389=0 & 
                                                                    n2_2389=n_2671 & 
                                                                    n2_2389=n2_2481 & 
                                                                    n2_2389=m_2670 & 
                                                                    n2_2389=m2_2480 & 
                                                                    n_2403=n1_2386 & 
                                                                    n_2382=n & 
                                                                    k_2423=n_2433 & 
                                                                    m_2402=m1_2385 & 
                                                                    flted_162_2422=m_2432 & 
                                                                    n1_2478=n_2562 & 
                                                                    m1_2477=m_2561 & 
                                                                    v_node_179_1095'=p_2476 & 
                                                                    (983::n1_2386=n-
                                                                    1 & 
                                                                    n2_2389<n | 
                                                                    n2_2389=n-
                                                                    1 & 
                                                                    n1_2386<=(n-
                                                                    2)) & 
                                                                    (1022::n1_2478=(0+
                                                                    2)-1 & 
                                                                    n_2433=0+
                                                                    2 & 
                                                                    m_2432=m2_2480+
                                                                    m1_2477+
                                                                    1 & 
                                                                    n_2475=0+
                                                                    2 & ((0+
                                                                    2)-
                                                                    2)<=n2_2481 & 
                                                                    0<=n2_2481 & 
                                                                    n2_2481<(0+
                                                                    2) & 
                                                                    0<=m1_2477 & 
                                                                    0<=m2_2480 & 
                                                                    v_node_173_2429!=null | 
                                                                    n2_2481=(0+
                                                                    2)-1 & 
                                                                    n1_2478=(0+
                                                                    2)-2 & 
                                                                    n_2433=0+
                                                                    2 & 
                                                                    m_2432=m2_2480+
                                                                    m1_2477+
                                                                    1 & 
                                                                    n_2475=0+
                                                                    2 & 
                                                                    0<=m1_2477 & 
                                                                    0<=m2_2480 & 
                                                                    2<=(0+
                                                                    2) & 
                                                                    v_node_173_2429!=null) & 
                                                                    (1110::n1_2637=v_int_177_2822-
                                                                    1 & 
                                                                    n_2562=v_int_177_2822 & 
                                                                    m_2561=m2_2639+
                                                                    m1_2636+
                                                                    1 & 
                                                                    n_2634=v_int_177_2822 & 
                                                                    (v_int_177_2822-
                                                                    2)<=n2_2640 & 
                                                                    0<=n2_2640 & 
                                                                    n2_2640<v_int_177_2822 & 
                                                                    0<=m1_2636 & 
                                                                    0<=m2_2639 & 
                                                                    p_2476!=null | 
                                                                    n2_2640=v_int_177_2822-
                                                                    1 & 
                                                                    n1_2637=v_int_177_2822-
                                                                    2 & 
                                                                    n_2562=v_int_177_2822 & 
                                                                    m_2561=m2_2639+
                                                                    m1_2636+
                                                                    1 & 
                                                                    n_2634=v_int_177_2822 & 
                                                                    0<=m1_2636 & 
                                                                    0<=m2_2639 & 
                                                                    2<=v_int_177_2822 & 
                                                                    p_2476!=null) & 
                                                                    0<=n_2562 & 
                                                                    null!=v_node_173_2429 & 
                                                                    m=1+
                                                                    m1_2385+
                                                                    m2_2388 & 
                                                                    (1+
                                                                    m2_2480)<=v_int_177_2822 & 
                                                                    0<=k_2423 & 
                                                                    (-1+
                                                                    n2_2389)<=n1_2386 & 
                                                                    (-1+
                                                                    n1_2386)<=n2_2389 & 
                                                                    0<=m2_2388 & 
                                                                    0!=flted_162_2422 & 
                                                                    0<=m_2561 & 
                                                                    -1+
                                                                    flted_162_2422=m_2402 & 
                                                                    0<=m & 
                                                                    0!=m & 
                                                                    0<=flted_162_2422 & 
                                                                    0!=k_2423 & 
                                                                    0!=n & 
                                                                    INS(k_2423,n_2403) & 
                                                                    0<=n1_2386 & 
                                                                    0<=n & 
                                                                    0<=m1_2385]
                                                                    [q_2479=null & 
                                                                    q_2479=v_node_179_1094']
                                                                    [!(v_bool_166_1325')]
                                                                    [null=tmp_79']
                                                                    [x'=x & 
                                                                    x'!=null]
                                                                    [a'=a & 
                                                                    a'<=Anon_2383]
                                                                    [v_bool_170_1324']
                                                                    [tmp_78'=p_2384]
                                                                    [q_2387=null & 
                                                                    q_2387=v_node_179_1093']
                                                                    [v_bool_175_1174']
                                                                    ))&{FLOW,(20,21)=__norm}
    es_infer_vars/rel: [x; a; INS]
    es_var_measures: MayLoop; 
x'::node<Anon_2383,n_2382,v_node_173_2429,q_2387>@M[Orig][] * v_node_173_2429::node<Anon_2474,n_2475,p_2476,q_2479>@I[Orig][] * q_2387::node<Anon_2521,n_2522,p_2523,q_2526>@I[Orig][] * p_2523::avl<m1_2524,n1_2525>@I[Orig]@ rem br[{651,650}] * q_2526::avl<m2_2527,n2_2528>@I[Orig]@ rem br[{651,650}] * p_2476::node<Anon_2650,n_2651,p_2652,q_2655>@I[Orig][] * p_2652::avl<m1_2653,n1_2654>@I[Orig]@ rem br[{651,650}] * q_2655::avl<m2_2656,n2_2657>@I[Orig]@ rem br[{651,650}] * q_2479::node<Anon_2779,n_2780,p_2781,q_2784>@I[Orig][] * p_2781::avl<m1_2782,n1_2783>@I[Orig]@ rem br[{651,650}] * q_2784::avl<m2_2785,n2_2786>@I[Orig]@ rem br[{651,650}]&(([
                                                                    v_bool_175_1174']
                                                                    [q_2387=v_node_179_1093' & 
                                                                    q_2479=v_node_179_1094' & 
                                                                    p_2476=v_node_179_1095' & 
                                                                    m_2670=m2_2480 & 
                                                                    n_2671=n2_2481 & 
                                                                    m_2561=m1_2477 & 
                                                                    n_2562=n1_2478 & 
                                                                    n_2403=n1_2386 & 
                                                                    n_2382=n & 
                                                                    k_2423=n_2433 & 
                                                                    m_2402=m1_2385 & 
                                                                    flted_162_2422=m_2432 & 
                                                                    n2_2389=n_2485 & 
                                                                    m2_2388=m_2484 & 
                                                                    (983::n1_2386=n-
                                                                    1 & 
                                                                    n2_2389<n | 
                                                                    n2_2389=n-
                                                                    1 & 
                                                                    n1_2386<=(n-
                                                                    2)) & 
                                                                    (1022::n1_2478=(v_int_175_2540+
                                                                    2)-1 & 
                                                                    n_2433=v_int_175_2540+
                                                                    2 & 
                                                                    m_2432=m2_2480+
                                                                    m1_2477+
                                                                    1 & 
                                                                    n_2475=v_int_175_2540+
                                                                    2 & 
                                                                    ((v_int_175_2540+
                                                                    2)-
                                                                    2)<=n2_2481 & 
                                                                    0<=n2_2481 & 
                                                                    n2_2481<(v_int_175_2540+
                                                                    2) & 
                                                                    0<=m1_2477 & 
                                                                    0<=m2_2480 & 
                                                                    v_node_173_2429!=null | 
                                                                    n2_2481=(v_int_175_2540+
                                                                    2)-1 & 
                                                                    n1_2478=(v_int_175_2540+
                                                                    2)-2 & 
                                                                    n_2433=v_int_175_2540+
                                                                    2 & 
                                                                    m_2432=m2_2480+
                                                                    m1_2477+
                                                                    1 & 
                                                                    n_2475=v_int_175_2540+
                                                                    2 & 
                                                                    0<=m1_2477 & 
                                                                    0<=m2_2480 & 
                                                                    2<=(v_int_175_2540+
                                                                    2) & 
                                                                    v_node_173_2429!=null) & 
                                                                    (1038::n1_2525=v_int_175_2540-
                                                                    1 & 
                                                                    n_2485=v_int_175_2540 & 
                                                                    m_2484=m2_2527+
                                                                    m1_2524+
                                                                    1 & 
                                                                    n_2522=v_int_175_2540 & 
                                                                    (v_int_175_2540-
                                                                    2)<=n2_2528 & 
                                                                    0<=n2_2528 & 
                                                                    n2_2528<v_int_175_2540 & 
                                                                    0<=m1_2524 & 
                                                                    0<=m2_2527 & 
                                                                    q_2387!=null | 
                                                                    n2_2528=v_int_175_2540-
                                                                    1 & 
                                                                    n1_2525=v_int_175_2540-
                                                                    2 & 
                                                                    n_2485=v_int_175_2540 & 
                                                                    m_2484=m2_2527+
                                                                    m1_2524+
                                                                    1 & 
                                                                    n_2522=v_int_175_2540 & 
                                                                    0<=m1_2524 & 
                                                                    0<=m2_2527 & 
                                                                    2<=v_int_175_2540 & 
                                                                    q_2387!=null) & 
                                                                    (1110::n1_2654=v_int_177_2826-
                                                                    1 & 
                                                                    n_2562=v_int_177_2826 & 
                                                                    m_2561=m2_2656+
                                                                    m1_2653+
                                                                    1 & 
                                                                    n_2651=v_int_177_2826 & 
                                                                    (v_int_177_2826-
                                                                    2)<=n2_2657 & 
                                                                    0<=n2_2657 & 
                                                                    n2_2657<v_int_177_2826 & 
                                                                    0<=m1_2653 & 
                                                                    0<=m2_2656 & 
                                                                    p_2476!=null | 
                                                                    n2_2657=v_int_177_2826-
                                                                    1 & 
                                                                    n1_2654=v_int_177_2826-
                                                                    2 & 
                                                                    n_2562=v_int_177_2826 & 
                                                                    m_2561=m2_2656+
                                                                    m1_2653+
                                                                    1 & 
                                                                    n_2651=v_int_177_2826 & 
                                                                    0<=m1_2653 & 
                                                                    0<=m2_2656 & 
                                                                    2<=v_int_177_2826 & 
                                                                    p_2476!=null) & 
                                                                    (1172::n1_2783=v_int_177_2827-
                                                                    1 & 
                                                                    n_2671=v_int_177_2827 & 
                                                                    m_2670=m2_2785+
                                                                    m1_2782+
                                                                    1 & 
                                                                    n_2780=v_int_177_2827 & 
                                                                    (v_int_177_2827-
                                                                    2)<=n2_2786 & 
                                                                    0<=n2_2786 & 
                                                                    n2_2786<v_int_177_2827 & 
                                                                    0<=m1_2782 & 
                                                                    0<=m2_2785 & 
                                                                    q_2479!=null | 
                                                                    n2_2786=v_int_177_2827-
                                                                    1 & 
                                                                    n1_2783=v_int_177_2827-
                                                                    2 & 
                                                                    n_2671=v_int_177_2827 & 
                                                                    m_2670=m2_2785+
                                                                    m1_2782+
                                                                    1 & 
                                                                    n_2780=v_int_177_2827 & 
                                                                    0<=m1_2782 & 
                                                                    0<=m2_2785 & 
                                                                    2<=v_int_177_2827 & 
                                                                    q_2479!=null) & 
                                                                    0<=n & 
                                                                    null!=v_node_173_2429 & 
                                                                    0<=m_2561 & 
                                                                    (-1+
                                                                    n1_2386)<=n2_2389 & 
                                                                    0<=k_2423 & 
                                                                    0<=m_2670 & 
                                                                    0!=n & 
                                                                    0<=n1_2386 & 
                                                                    (-1+
                                                                    n2_2389)<=n1_2386 & 
                                                                    -1+
                                                                    flted_162_2422=m_2402 & 
                                                                    0<=n_2671 & 
                                                                    0<=n2_2389 & 
                                                                    (1+
                                                                    v_int_177_2827)<=v_int_177_2826 & 
                                                                    0!=k_2423 & 
                                                                    0<=m2_2388 & 
                                                                    m=1+
                                                                    m1_2385+
                                                                    m2_2388 & 
                                                                    0<=m & 
                                                                    0!=flted_162_2422 & 
                                                                    0<=flted_162_2422 & 
                                                                    0<=n_2562 & 
                                                                    0<=m1_2385 & 
                                                                    INS(k_2423,n_2403) & 
                                                                    0!=m]
                                                                    [!(v_bool_166_1325')]
                                                                    [null=tmp_79']
                                                                    [x'=x & 
                                                                    x'!=null]
                                                                    [a'=a & 
                                                                    a'<=Anon_2383]
                                                                    [v_bool_170_1324']
                                                                    [tmp_78'=p_2384]
                                                                    [v_bool_177_1172']
                                                                    ))&{FLOW,(20,21)=__norm}
es_infer_vars/rel: [x; a; INS]
es_var_measures: MayLoop]] has failed 


Procedure Call:avl_msh.ss:200: 12: 
Verification Context:(Line:162,Col:10)
Proving precondition in method rotate_left$node~node~node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[lm; rlm; ln; 
                  rrm](ex)v_node_200_1244'::avl<lm,ln>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  v_node_200_1243'::avl<rlm,ln_116>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                  v_node_200_1242'::avl<rrm,flted_36_115>@M[Orig][LHSCase]@ rem br[{650}]&
                  (
                  ([1+ln=flted_36_115 & 1<=flted_36_115 & 1+
                     ln_116=flted_36_115]
                   [0<=lm][0<=rlm][1<=rrm][v_node_200_1242'!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              EXISTS(flted_37_2270,
                              k_2271: res::avl<flted_37_2270,k_2271>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([flted_37_2270=2+lm+rlm+rrm & 0<=lm & 
                                 0<=rlm & 0<=rrm & 1<=rrm]
                               [v_node_200_1242'!=null][-2+k_2271=ln & 0<=ln]
                               [res!=null][0<=flted_36_115][0<=ln_116]))&
                              {FLOW,(20,21)=__norm}))
Current States: [ or[x'::node<Anon_2383,n_2382,p_2384,v_node_195_3493>@M[Orig][] * v_node_195_3493::node<Anon_3538,n_3539,p_3540,q_3543>@I[Orig][] * q_3543::node<Anon_3697,n_3698,p_3699,q_3702>@I[Orig][] * p_3699::avl<m1_3700,n1_3701>@I[Orig]@ rem br[{651,650}] * q_3702::avl<m2_3703,n2_3704>@I[Orig]@ rem br[{651,650}]&(([
                                                                    v_bool_198_1321']
                                                                    [q_3543=v_node_200_1242' & 
                                                                    m_3625=m2_3544 & 
                                                                    n_3626=n2_3545 & 
                                                                    m_3496=flted_162_3486 & 
                                                                    m2_2388=m_3466 & 
                                                                    n_3497=k_3487 & 
                                                                    n=n_2382 & 
                                                                    n2_2389=n_3467 & 
                                                                    n_3549=n1_2386 & 
                                                                    n_3549=m_3548 & 
                                                                    n_3549=m1_2385 & 
                                                                    n_3549=0 & 
                                                                    n_3549=n_3735 & 
                                                                    n_3549=n1_3542 & 
                                                                    n_3549=m_3734 & 
                                                                    n_3549=m1_3541 & 
                                                                    (983::n1_2386=n-
                                                                    1 & 
                                                                    n2_2389<n | 
                                                                    n2_2389=n-
                                                                    1 & 
                                                                    n1_2386<=(n-
                                                                    2)) & 
                                                                    (1846::n1_3542=(0+
                                                                    2)-1 & 
                                                                    n_3497=0+
                                                                    2 & 
                                                                    m_3496=m2_3544+
                                                                    m1_3541+
                                                                    1 & 
                                                                    n_3539=0+
                                                                    2 & ((0+
                                                                    2)-
                                                                    2)<=n2_3545 & 
                                                                    0<=n2_3545 & 
                                                                    n2_3545<(0+
                                                                    2) & 
                                                                    0<=m1_3541 & 
                                                                    0<=m2_3544 & 
                                                                    v_node_195_3493!=null | 
                                                                    n2_3545=(0+
                                                                    2)-1 & 
                                                                    n1_3542=(0+
                                                                    2)-2 & 
                                                                    n_3497=0+
                                                                    2 & 
                                                                    m_3496=m2_3544+
                                                                    m1_3541+
                                                                    1 & 
                                                                    n_3539=0+
                                                                    2 & 
                                                                    0<=m1_3541 & 
                                                                    0<=m2_3544 & 
                                                                    2<=(0+
                                                                    2) & 
                                                                    v_node_195_3493!=null) & 
                                                                    (1934::n1_3701=v_int_198_3886-
                                                                    1 & 
                                                                    n_3626=v_int_198_3886 & 
                                                                    m_3625=m2_3703+
                                                                    m1_3700+
                                                                    1 & 
                                                                    n_3698=v_int_198_3886 & 
                                                                    (v_int_198_3886-
                                                                    2)<=n2_3704 & 
                                                                    0<=n2_3704 & 
                                                                    n2_3704<v_int_198_3886 & 
                                                                    0<=m1_3700 & 
                                                                    0<=m2_3703 & 
                                                                    q_3543!=null | 
                                                                    n2_3704=v_int_198_3886-
                                                                    1 & 
                                                                    n1_3701=v_int_198_3886-
                                                                    2 & 
                                                                    n_3626=v_int_198_3886 & 
                                                                    m_3625=m2_3703+
                                                                    m1_3700+
                                                                    1 & 
                                                                    n_3698=v_int_198_3886 & 
                                                                    0<=m1_3700 & 
                                                                    0<=m2_3703 & 
                                                                    2<=v_int_198_3886 & 
                                                                    q_3543!=null) & 
                                                                    0<=flted_162_3486 & 
                                                                    0<=m2_2388 & 
                                                                    INS(k_3487,n_3467) & 
                                                                    0<=m & 
                                                                    0<=n2_2389 & 
                                                                    0!=n & 
                                                                    0!=m & 
                                                                    0<=m_3625 & 
                                                                    -1+
                                                                    flted_162_3486=m_3466 & 
                                                                    null!=v_node_195_3493 & 
                                                                    (1+
                                                                    m1_3541)<=v_int_198_3886 & 
                                                                    0<=n & 
                                                                    (-1+
                                                                    n1_2386)<=n2_2389 & 
                                                                    m=1+
                                                                    m1_2385+
                                                                    m2_2388 & 
                                                                    0<=n_3626 & 
                                                                    0<=k_3487 & 
                                                                    0<=m1_2385 & 
                                                                    0!=k_3487 & 
                                                                    (-1+
                                                                    n2_2389)<=n1_2386 & 
                                                                    0!=flted_162_3486]
                                                                    [p_3540=null & 
                                                                    p_3540=v_node_200_1243']
                                                                    [!(v_bool_166_1325')]
                                                                    [tmp_79'=null]
                                                                    [x=x' & 
                                                                    x'!=null]
                                                                    [a=a' & 
                                                                    (1+
                                                                    Anon_2383)<=a']
                                                                    [!(v_bool_170_1324')]
                                                                    [q_2387=tmp_78']
                                                                    [p_2384=null & 
                                                                    p_2384=v_node_200_1244']
                                                                    [v_bool_196_1323']
                                                                    ))&{FLOW,(20,21)=__norm}
    es_infer_vars/rel: [x; a; INS]
    es_var_measures: MayLoop; 
x'::node<Anon_2383,n_2382,p_2384,v_node_195_3493>@M[Orig][] * v_node_195_3493::node<Anon_3538,n_3539,p_3540,q_3543>@I[Orig][] * p_2384::node<Anon_3585,n_3586,p_3587,q_3590>@I[Orig][] * p_3587::avl<m1_3588,n1_3589>@I[Orig]@ rem br[{651,650}] * q_3590::avl<m2_3591,n2_3592>@I[Orig]@ rem br[{651,650}] * q_3543::node<Anon_3714,n_3715,p_3716,q_3719>@I[Orig][] * p_3716::avl<m1_3717,n1_3718>@I[Orig]@ rem br[{651,650}] * q_3719::avl<m2_3720,n2_3721>@I[Orig]@ rem br[{651,650}] * p_3540::node<Anon_3843,n_3844,p_3845,q_3848>@I[Orig][] * p_3845::avl<m1_3846,n1_3847>@I[Orig]@ rem br[{651,650}] * q_3848::avl<m2_3849,n2_3850>@I[Orig]@ rem br[{651,650}]&(([
                                                                    v_bool_196_1323']
                                                                    [q_3543=v_node_200_1242' & 
                                                                    p_3540=v_node_200_1243' & 
                                                                    p_2384=v_node_200_1244' & 
                                                                    m_3734=m1_3541 & 
                                                                    n_3735=n1_3542 & 
                                                                    m_3625=m2_3544 & 
                                                                    n_3626=n2_3545 & 
                                                                    n_3467=n2_2389 & 
                                                                    n_2382=n & 
                                                                    k_3487=n_3497 & 
                                                                    m_3466=m2_2388 & 
                                                                    flted_162_3486=m_3496 & 
                                                                    n1_2386=n_3549 & 
                                                                    m1_2385=m_3548 & 
                                                                    (983::n1_2386=n-
                                                                    1 & 
                                                                    n2_2389<n | 
                                                                    n2_2389=n-
                                                                    1 & 
                                                                    n1_2386<=(n-
                                                                    2)) & 
                                                                    (1846::n1_3542=(v_int_196_3604+
                                                                    2)-1 & 
                                                                    n_3497=v_int_196_3604+
                                                                    2 & 
                                                                    m_3496=m2_3544+
                                                                    m1_3541+
                                                                    1 & 
                                                                    n_3539=v_int_196_3604+
                                                                    2 & 
                                                                    ((v_int_196_3604+
                                                                    2)-
                                                                    2)<=n2_3545 & 
                                                                    0<=n2_3545 & 
                                                                    n2_3545<(v_int_196_3604+
                                                                    2) & 
                                                                    0<=m1_3541 & 
                                                                    0<=m2_3544 & 
                                                                    v_node_195_3493!=null | 
                                                                    n2_3545=(v_int_196_3604+
                                                                    2)-1 & 
                                                                    n1_3542=(v_int_196_3604+
                                                                    2)-2 & 
                                                                    n_3497=v_int_196_3604+
                                                                    2 & 
                                                                    m_3496=m2_3544+
                                                                    m1_3541+
                                                                    1 & 
                                                                    n_3539=v_int_196_3604+
                                                                    2 & 
                                                                    0<=m1_3541 & 
                                                                    0<=m2_3544 & 
                                                                    2<=(v_int_196_3604+
                                                                    2) & 
                                                                    v_node_195_3493!=null) & 
                                                                    (1862::n1_3589=v_int_196_3604-
                                                                    1 & 
                                                                    n_3549=v_int_196_3604 & 
                                                                    m_3548=m2_3591+
                                                                    m1_3588+
                                                                    1 & 
                                                                    n_3586=v_int_196_3604 & 
                                                                    (v_int_196_3604-
                                                                    2)<=n2_3592 & 
                                                                    0<=n2_3592 & 
                                                                    n2_3592<v_int_196_3604 & 
                                                                    0<=m1_3588 & 
                                                                    0<=m2_3591 & 
                                                                    p_2384!=null | 
                                                                    n2_3592=v_int_196_3604-
                                                                    1 & 
                                                                    n1_3589=v_int_196_3604-
                                                                    2 & 
                                                                    n_3549=v_int_196_3604 & 
                                                                    m_3548=m2_3591+
                                                                    m1_3588+
                                                                    1 & 
                                                                    n_3586=v_int_196_3604 & 
                                                                    0<=m1_3588 & 
                                                                    0<=m2_3591 & 
                                                                    2<=v_int_196_3604 & 
                                                                    p_2384!=null) & 
                                                                    (1934::n1_3718=v_int_198_3890-
                                                                    1 & 
                                                                    n_3626=v_int_198_3890 & 
                                                                    m_3625=m2_3720+
                                                                    m1_3717+
                                                                    1 & 
                                                                    n_3715=v_int_198_3890 & 
                                                                    (v_int_198_3890-
                                                                    2)<=n2_3721 & 
                                                                    0<=n2_3721 & 
                                                                    n2_3721<v_int_198_3890 & 
                                                                    0<=m1_3717 & 
                                                                    0<=m2_3720 & 
                                                                    q_3543!=null | 
                                                                    n2_3721=v_int_198_3890-
                                                                    1 & 
                                                                    n1_3718=v_int_198_3890-
                                                                    2 & 
                                                                    n_3626=v_int_198_3890 & 
                                                                    m_3625=m2_3720+
                                                                    m1_3717+
                                                                    1 & 
                                                                    n_3715=v_int_198_3890 & 
                                                                    0<=m1_3717 & 
                                                                    0<=m2_3720 & 
                                                                    2<=v_int_198_3890 & 
                                                                    q_3543!=null) & 
                                                                    (1996::n1_3847=v_int_198_3891-
                                                                    1 & 
                                                                    n_3735=v_int_198_3891 & 
                                                                    m_3734=m2_3849+
                                                                    m1_3846+
                                                                    1 & 
                                                                    n_3844=v_int_198_3891 & 
                                                                    (v_int_198_3891-
                                                                    2)<=n2_3850 & 
                                                                    0<=n2_3850 & 
                                                                    n2_3850<v_int_198_3891 & 
                                                                    0<=m1_3846 & 
                                                                    0<=m2_3849 & 
                                                                    p_3540!=null | 
                                                                    n2_3850=v_int_198_3891-
                                                                    1 & 
                                                                    n1_3847=v_int_198_3891-
                                                                    2 & 
                                                                    n_3735=v_int_198_3891 & 
                                                                    m_3734=m2_3849+
                                                                    m1_3846+
                                                                    1 & 
                                                                    n_3844=v_int_198_3891 & 
                                                                    0<=m1_3846 & 
                                                                    0<=m2_3849 & 
                                                                    2<=v_int_198_3891 & 
                                                                    p_3540!=null) & 
                                                                    0<=n_3735 & 
                                                                    (-1+
                                                                    n1_2386)<=n2_2389 & 
                                                                    0!=m & 
                                                                    0<=m_3625 & 
                                                                    0<=n1_2386 & 
                                                                    0<=m1_2385 & 
                                                                    0!=n & 
                                                                    -1+
                                                                    flted_162_3486=m_3466 & 
                                                                    (-1+
                                                                    n2_2389)<=n1_2386 & 
                                                                    null!=v_node_195_3493 & 
                                                                    0<=n_3626 & 
                                                                    INS(k_3487,n_3467) & 
                                                                    0<=n & 
                                                                    0<=m & 
                                                                    (1+
                                                                    v_int_198_3891)<=v_int_198_3890 & 
                                                                    0!=k_3487 & 
                                                                    0<=m2_2388 & 
                                                                    m=1+
                                                                    m1_2385+
                                                                    m2_2388 & 
                                                                    0<=m_3734 & 
                                                                    0!=flted_162_3486 & 
                                                                    0<=n2_2389 & 
                                                                    0<=flted_162_3486 & 
                                                                    0<=k_3487]
                                                                    [!(v_bool_166_1325')]
                                                                    [null=tmp_79']
                                                                    [x'=x & 
                                                                    x'!=null]
                                                                    [a'=a & 
                                                                    (1+
                                                                    Anon_2383)<=a']
                                                                    [!(v_bool_170_1324')]
                                                                    [tmp_78'=q_2387]
                                                                    [v_bool_198_1321']
                                                                    ))&{FLOW,(20,21)=__norm}
es_infer_vars/rel: [x; a; INS]
es_var_measures: MayLoop]] has failed 


!!! OLD SPECS: ((None,[]),EInfer [INS,x,a]
              EBase exists (Expl)(Impl)[m; 
                    n](ex)x::avl<m,n>@M[Orig][LHSCase]@ rem br[{651,650}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::
                                EXISTS(flted_162_77,
                                k: res::avl<flted_162_77,k>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                (
                                ([0<=flted_162_77 & -1+flted_162_77=m]
                                 [0<=k & INS(k,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  n](ex)x::avl<m,n>@M[Orig][LHSCase]@ rem br[{651,650}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 53::
                              EXISTS(flted_162_4527,
                              k_4528: res::avl<flted_162_4527,k_4528>@M[Orig][LHSCase]@ rem br[{651,650}]&
                              (
                              ([1+m=flted_162_4527 & 0<=m & 0<=flted_162_4527]
                               [0<=k_4528 & 0<=n & INS(k_4528,n)]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int result FAIL-1

Checking procedure insert_inline$node~int... 
Procedure Call:avl_msh.ss:242: 30: 
Verification Context:(Line:219,Col:10)
Proving precondition in method height$node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[m_5219; 
                  n_5220](ex)v_node_242_741'::avl<m_5219,n_5220>@I[Orig][LHSCase]@ rem br[{651,650}]&
                  (([0<=m_5219][0<=n_5220]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(
                              ([null=v_node_242_741'][0=m_5219 & 0<=m_5219]
                               [0=n_5220 & 0<=n_5220][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1859,n_1860,p_1861,m1_1862,
                                 n1_1863,q_1864,m2_1865,
                                 n2_1866: v_node_242_741'::node<Anon_1859,n_1860,p_1861,q_1864>@I[Orig][] * 
                                 p_1861::avl<m1_1862,n1_1863>@I[Orig]@ rem br[{651,650}] * 
                                 q_1864::avl<m2_1865,n2_1866>@I[Orig]@ rem br[{651,650}]&
                                 (
                                 ([(n1_1863=res-1 & n_5220=res & 
                                    m_5219=m2_1865+m1_1862+1 & n_1860=res & 
                                    (res-2)<=n2_1866 & 0<=n2_1866 & 
                                    n2_1866<res & 0<=m1_1862 & 0<=m2_1865 & 
                                    v_node_242_741'!=null | n2_1866=res-1 & 
                                    n1_1863=res-2 & n_5220=res & 
                                    m_5219=m2_1865+m1_1862+1 & n_1860=res & 
                                    0<=m1_1862 & 0<=m2_1865 & 2<=res & 
                                    v_node_242_741'!=null) & 0<=m_5219 & 
                                    0<=n_5220]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
Current States: [ p_4660::node<Anon_4834,n_4835,p_4836,q_4839>@I[Orig][] * p_4836::avl<m1_4837,n1_4838>@I[Orig]@ rem br[{651,650}] * q_4839::avl<m2_4840,n2_4841>@I[Orig]@ rem br[{651,650}] * q_4663::node<Anon_5096,n_5097,p_5098,q_5101>@I[Orig][] * p_5098::avl<m1_5099,n1_5100>@I[Orig]@ rem br[{651,650}] * q_5101::avl<m2_5102,n2_5103>@I[Orig]@ rem br[{651,650}] * q_4571::node<Anon_5173,n_5174,p_5175,q_5178>@I[Orig][] * p_5175::avl<m1_5176,n1_5177>@I[Orig]@ rem br[{651,650}] * q_5178::avl<m2_5179,n2_5180>@I[Orig]@ rem br[{651,650}] * k1_68'::node<val_239_5207,height_239_5206,left_239_5205,x>@M[Orig][] * x'::node<Anon_4567,h_72',q_4663,q_4571>@M[Orig][]&(([
                                                                    v_node_242_741'=left_239_5205]
                                                                    [n_5108=n_4706 & 
                                                                    m2_5127=m2_4711 & 
                                                                    n2_5128=n2_4712 & 
                                                                    m1_5124=m1_4708 & 
                                                                    n1_5125=n1_4709 & 
                                                                    n_5024=n_4956 & 
                                                                    m2_5043=m2_4961 & 
                                                                    n2_5044=n2_4962 & 
                                                                    m1_5040=m1_4958 & 
                                                                    n1_5041=n1_4959 & 
                                                                    m_4846=m2_4664 & 
                                                                    n_4847=n2_4665 & 
                                                                    m_4745=m1_4661 & 
                                                                    n_4746=n1_4662 & 
                                                                    v_node_231_4613=k1_68' & 
                                                                    n_4587=n1_4570 & 
                                                                    n_4566=n & 
                                                                    n1_4607=n_4617 & 
                                                                    m_4586=m1_4569 & 
                                                                    flted_219_4606=m_4616 & 
                                                                    n2_4573=n_4669 & 
                                                                    m2_4572=m_4668 & 
                                                                    (2654::n1_4570=n-
                                                                    1 & 
                                                                    n2_4573<n | 
                                                                    n2_4573=n-
                                                                    1 & 
                                                                    n1_4570<=(n-
                                                                    2)) & 
                                                                    (2693::n1_4662=(v_int_232_4724+
                                                                    2)-1 & 
                                                                    n_4617=v_int_232_4724+
                                                                    2 & 
                                                                    m_4616=m2_4664+
                                                                    m1_4661+
                                                                    1 & 
                                                                    n_4659=v_int_232_4724+
                                                                    2 & 
                                                                    ((v_int_232_4724+
                                                                    2)-
                                                                    2)<=n2_4665 & 
                                                                    0<=n2_4665 & 
                                                                    n2_4665<(v_int_232_4724+
                                                                    2) & 
                                                                    0<=m1_4661 & 
                                                                    0<=m2_4664 & 
                                                                    v_node_231_4613!=null | 
                                                                    n2_4665=(v_int_232_4724+
                                                                    2)-1 & 
                                                                    n1_4662=(v_int_232_4724+
                                                                    2)-2 & 
                                                                    n_4617=v_int_232_4724+
                                                                    2 & 
                                                                    m_4616=m2_4664+
                                                                    m1_4661+
                                                                    1 & 
                                                                    n_4659=v_int_232_4724+
                                                                    2 & 
                                                                    0<=m1_4661 & 
                                                                    0<=m2_4664 & 
                                                                    2<=(v_int_232_4724+
                                                                    2) & 
                                                                    v_node_231_4613!=null) & 
                                                                    (2709::n1_4709=v_int_232_4724-
                                                                    1 & 
                                                                    n_4669=v_int_232_4724 & 
                                                                    m_4668=m2_4711+
                                                                    m1_4708+
                                                                    1 & 
                                                                    n_4706=v_int_232_4724 & 
                                                                    (v_int_232_4724-
                                                                    2)<=n2_4712 & 
                                                                    0<=n2_4712 & 
                                                                    n2_4712<v_int_232_4724 & 
                                                                    0<=m1_4708 & 
                                                                    0<=m2_4711 & 
                                                                    q_4571!=null | 
                                                                    n2_4712=v_int_232_4724-
                                                                    1 & 
                                                                    n1_4709=v_int_232_4724-
                                                                    2 & 
                                                                    n_4669=v_int_232_4724 & 
                                                                    m_4668=m2_4711+
                                                                    m1_4708+
                                                                    1 & 
                                                                    n_4706=v_int_232_4724 & 
                                                                    0<=m1_4708 & 
                                                                    0<=m2_4711 & 
                                                                    2<=v_int_232_4724 & 
                                                                    q_4571!=null) & 
                                                                    (2781::n1_4838=v_int_235_5002-
                                                                    1 & 
                                                                    n_4746=v_int_235_5002 & 
                                                                    m_4745=m2_4840+
                                                                    m1_4837+
                                                                    1 & 
                                                                    n_4835=v_int_235_5002 & 
                                                                    (v_int_235_5002-
                                                                    2)<=n2_4841 & 
                                                                    0<=n2_4841 & 
                                                                    n2_4841<v_int_235_5002 & 
                                                                    0<=m1_4837 & 
                                                                    0<=m2_4840 & 
                                                                    p_4660!=null | 
                                                                    n2_4841=v_int_235_5002-
                                                                    1 & 
                                                                    n1_4838=v_int_235_5002-
                                                                    2 & 
                                                                    n_4746=v_int_235_5002 & 
                                                                    m_4745=m2_4840+
                                                                    m1_4837+
                                                                    1 & 
                                                                    n_4835=v_int_235_5002 & 
                                                                    0<=m1_4837 & 
                                                                    0<=m2_4840 & 
                                                                    2<=v_int_235_5002 & 
                                                                    p_4660!=null) & 
                                                                    (2821::n1_4959=v_int_235_5003-
                                                                    1 & 
                                                                    n_4847=v_int_235_5003 & 
                                                                    m_4846=m2_4961+
                                                                    m1_4958+
                                                                    1 & 
                                                                    n_4956=v_int_235_5003 & 
                                                                    (v_int_235_5003-
                                                                    2)<=n2_4962 & 
                                                                    0<=n2_4962 & 
                                                                    n2_4962<v_int_235_5003 & 
                                                                    0<=m1_4958 & 
                                                                    0<=m2_4961 & 
                                                                    q_4663!=null | 
                                                                    n2_4962=v_int_235_5003-
                                                                    1 & 
                                                                    n1_4959=v_int_235_5003-
                                                                    2 & 
                                                                    n_4847=v_int_235_5003 & 
                                                                    m_4846=m2_4961+
                                                                    m1_4958+
                                                                    1 & 
                                                                    n_4956=v_int_235_5003 & 
                                                                    0<=m1_4958 & 
                                                                    0<=m2_4961 & 
                                                                    2<=v_int_235_5003 & 
                                                                    q_4663!=null) & 
                                                                    (2947::n1_5041=n_4956-
                                                                    1 & 
                                                                    n2_5044<n_4956 | 
                                                                    n2_5044=n_4956-
                                                                    1 & 
                                                                    n1_5041<=(n_4956-
                                                                    2)) & 
                                                                    (2947::n1_5041=n_5024-
                                                                    1 & 
                                                                    n2_5044<n_5024 | 
                                                                    n2_5044=n_5024-
                                                                    1 & 
                                                                    n1_5041<=(n_5024-
                                                                    2)) & 
                                                                    (2943::n1_5100=v_int_238_5191-
                                                                    1 & 
                                                                    n_5024=v_int_238_5191 & 
                                                                    m_5023=m2_5102+
                                                                    m1_5099+
                                                                    1 & 
                                                                    n_5097=v_int_238_5191 & 
                                                                    (v_int_238_5191-
                                                                    2)<=n2_5103 & 
                                                                    0<=n2_5103 & 
                                                                    n2_5103<v_int_238_5191 & 
                                                                    0<=m1_5099 & 
                                                                    0<=m2_5102 & 
                                                                    q_4663!=null | 
                                                                    n2_5103=v_int_238_5191-
                                                                    1 & 
                                                                    n1_5100=v_int_238_5191-
                                                                    2 & 
                                                                    n_5024=v_int_238_5191 & 
                                                                    m_5023=m2_5102+
                                                                    m1_5099+
                                                                    1 & 
                                                                    n_5097=v_int_238_5191 & 
                                                                    0<=m1_5099 & 
                                                                    0<=m2_5102 & 
                                                                    2<=v_int_238_5191 & 
                                                                    q_4663!=null) & 
                                                                    (2989::n1_5125=n_4706-
                                                                    1 & 
                                                                    n2_5128<n_4706 | 
                                                                    n2_5128=n_4706-
                                                                    1 & 
                                                                    n1_5125<=(n_4706-
                                                                    2)) & 
                                                                    (2989::n1_5125=n_5108-
                                                                    1 & 
                                                                    n2_5128<n_5108 | 
                                                                    n2_5128=n_5108-
                                                                    1 & 
                                                                    n1_5125<=(n_5108-
                                                                    2)) & 
                                                                    (2985::n1_5177=v_int_238_5192-
                                                                    1 & 
                                                                    n_5108=v_int_238_5192 & 
                                                                    m_5107=m2_5179+
                                                                    m1_5176+
                                                                    1 & 
                                                                    n_5174=v_int_238_5192 & 
                                                                    (v_int_238_5192-
                                                                    2)<=n2_5180 & 
                                                                    0<=n2_5180 & 
                                                                    n2_5180<v_int_238_5192 & 
                                                                    0<=m1_5176 & 
                                                                    0<=m2_5179 & 
                                                                    q_4571!=null | 
                                                                    n2_5180=v_int_238_5192-
                                                                    1 & 
                                                                    n1_5177=v_int_238_5192-
                                                                    2 & 
                                                                    n_5108=v_int_238_5192 & 
                                                                    m_5107=m2_5179+
                                                                    m1_5176+
                                                                    1 & 
                                                                    n_5174=v_int_238_5192 & 
                                                                    0<=m1_5176 & 
                                                                    0<=m2_5179 & 
                                                                    2<=v_int_238_5192 & 
                                                                    q_4571!=null) & 
                                                                    h_5213=max(v_int_238_5191,
                                                                    v_int_238_5192) & 
                                                                    0<=m2_4572 & 
                                                                    0<=n_4746 & 
                                                                    m_5107=1+
                                                                    m1_5124+
                                                                    m2_5127 & 
                                                                    0<=flted_219_4606 & 
                                                                    0<=n_5024 & 
                                                                    (-1+
                                                                    n2_4573)<=n1_4570 & 
                                                                    h_72'=h_5213+
                                                                    1 & (-1+
                                                                    n1_4570)<=n2_4573 & 
                                                                    0!=flted_219_4606 & 
                                                                    0<=m_5107 & 
                                                                    0<=m & 
                                                                    0!=m & 
                                                                    (-1+
                                                                    n1_4607)<=n_4587 & 
                                                                    0<=n_5108 & 
                                                                    0<=n2_4573 & 
                                                                    q_4663!=null & 
                                                                    (-1+
                                                                    n2_5044)<=n1_5041 & 
                                                                    (-1+
                                                                    n1_5041)<=n2_5044 & 
                                                                    m=1+
                                                                    m1_4569+
                                                                    m2_4572 & 
                                                                    0!=n & 
                                                                    0<=n_4847 & 
                                                                    0<=n1_4570 & 
                                                                    0<=m_4745 & 
                                                                    (1+
                                                                    v_int_235_5003)<=v_int_235_5002 & 
                                                                    (-1+
                                                                    n1_5125)<=n2_5128 & 
                                                                    q_4571!=null & 
                                                                    m_5023=1+
                                                                    m1_5040+
                                                                    m2_5043 & 
                                                                    0<=m_4846 & 
                                                                    0<=n1_4607 & 
                                                                    0<=m_5023 & 
                                                                    n_4587<=n1_4607 & 
                                                                    -1+
                                                                    flted_219_4606=m_4586 & 
                                                                    (-1+
                                                                    n2_5128)<=n1_5125 & 
                                                                    0!=n1_4607 & 
                                                                    0<=n & 
                                                                    0<=m1_4569 & 
                                                                    null!=v_node_231_4613]
                                                                    [v_bool_232_839']
                                                                    [!(v_bool_224_1008')]
                                                                    [null=tmp_71']
                                                                    [x=x' & 
                                                                    x'!=null]
                                                                    [a'=a & 
                                                                    a'<=Anon_4567]
                                                                    [v_bool_228_1007']
                                                                    [tmp_69'=p_4568]
                                                                    [v_bool_235_837']
                                                                    [q_4960=q_5042]
                                                                    [p_4957=p_5039]
                                                                    [Anon_5038=Anon_4955]
                                                                    [q_4710=q_5126]
                                                                    [p_4707=p_5123]
                                                                    [Anon_5122=Anon_4705]
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure Call:avl_msh.ss:256: 28: 
Verification Context:(Line:219,Col:10)
Proving precondition in method height$node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[m_5739; 
                  n_5740](ex)v_node_256_798'::avl<m_5739,n_5740>@I[Orig][LHSCase]@ rem br[{651,650}]&
                  (([0<=m_5739][0<=n_5740]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(
                              ([null=v_node_256_798'][0=m_5739 & 0<=m_5739]
                               [0=n_5740 & 0<=n_5740][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1859,n_1860,p_1861,m1_1862,
                                 n1_1863,q_1864,m2_1865,
                                 n2_1866: v_node_256_798'::node<Anon_1859,n_1860,p_1861,q_1864>@I[Orig][] * 
                                 p_1861::avl<m1_1862,n1_1863>@I[Orig]@ rem br[{651,650}] * 
                                 q_1864::avl<m2_1865,n2_1866>@I[Orig]@ rem br[{651,650}]&
                                 (
                                 ([(n1_1863=res-1 & n_5740=res & 
                                    m_5739=m2_1865+m1_1862+1 & n_1860=res & 
                                    (res-2)<=n2_1866 & 0<=n2_1866 & 
                                    n2_1866<res & 0<=m1_1862 & 0<=m2_1865 & 
                                    v_node_256_798'!=null | n2_1866=res-1 & 
                                    n1_1863=res-2 & n_5740=res & 
                                    m_5739=m2_1865+m1_1862+1 & n_1860=res & 
                                    0<=m1_1862 & 0<=m2_1865 & 2<=res & 
                                    v_node_256_798'!=null) & 0<=m_5739 & 
                                    0<=n_5740]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
Current States: [ q_4571::node<Anon_4705,n_4706,p_4707,q_4710>@I[Orig][] * p_4707::avl<m1_4708,n1_4709>@I[Orig]@ rem br[{651,650}] * q_4710::avl<m2_4711,n2_4712>@I[Orig]@ rem br[{651,650}] * p_4660::node<Anon_5393,n_5394,p_5395,q_5398>@I[Orig][] * p_5395::avl<m1_5396,n1_5397>@I[Orig]@ rem br[{651,650}] * q_5398::avl<m2_5399,n2_5400>@I[Orig]@ rem br[{651,650}] * q_5608::avl<m2_5607,n2_5606>@I[Orig]@ rem br[{651,650}] * x'::node<Anon_4567,n_4566,q_5608,q_4571>@M[Orig][] * k1_68'::node<val_253_5669,height_253_5670,left_253_5671,p_5611>@M[Orig][] * p_5611::node<Anon_5717,n_5718,p_5719,q_5722>@I[Orig][] * p_5719::avl<m1_5720,n1_5721>@I[Orig]@ rem br[{651,650}] * q_5722::avl<m2_5723,n2_5724>@I[Orig]@ rem br[{651,650}] * k2_70'::node<val_255_5734,height_255_5735,v_node_231_4613,right_255_5736>@M[Orig][]&(([
                                                                    v_node_256_798'=right_255_5736]
                                                                    [m_5674=m1_5610 & 
                                                                    n_5675=n1_5609 & 
                                                                    q_4663=k2_70' & 
                                                                    m_4668=m2_4572 & 
                                                                    n_4669=n2_4573 & 
                                                                    m_4616=flted_219_4606 & 
                                                                    m1_4569=m_4586 & 
                                                                    n_4617=n1_4607 & 
                                                                    n=n_4566 & 
                                                                    n1_4570=n_4587 & 
                                                                    k1_68'=v_node_231_4613 & 
                                                                    n1_4662=n_4746 & 
                                                                    m1_4661=m_4745 & 
                                                                    n2_4665=n_4847 & 
                                                                    m2_4664=m_4846 & 
                                                                    n1_4838=n1_5304 & 
                                                                    m1_4837=m1_5303 & 
                                                                    n2_4841=n2_5307 & 
                                                                    m2_4840=m2_5306 & 
                                                                    n_4835=n_5252 & 
                                                                    n1_4975=n1_5482 & 
                                                                    m1_4974=m1_5481 & 
                                                                    n2_4978=n2_5485 & 
                                                                    m2_4977=m2_5484 & 
                                                                    n_4972=n_5406 & 
                                                                    (2654::n1_4570=n-
                                                                    1 & 
                                                                    n2_4573<n | 
                                                                    n2_4573=n-
                                                                    1 & 
                                                                    n1_4570<=(n-
                                                                    2)) & 
                                                                    (2693::n1_4662=(v_int_232_4724+
                                                                    2)-1 & 
                                                                    n_4617=v_int_232_4724+
                                                                    2 & 
                                                                    m_4616=m2_4664+
                                                                    m1_4661+
                                                                    1 & 
                                                                    n_4659=v_int_232_4724+
                                                                    2 & 
                                                                    ((v_int_232_4724+
                                                                    2)-
                                                                    2)<=n2_4665 & 
                                                                    0<=n2_4665 & 
                                                                    n2_4665<(v_int_232_4724+
                                                                    2) & 
                                                                    0<=m1_4661 & 
                                                                    0<=m2_4664 & 
                                                                    v_node_231_4613!=null | 
                                                                    n2_4665=(v_int_232_4724+
                                                                    2)-1 & 
                                                                    n1_4662=(v_int_232_4724+
                                                                    2)-2 & 
                                                                    n_4617=v_int_232_4724+
                                                                    2 & 
                                                                    m_4616=m2_4664+
                                                                    m1_4661+
                                                                    1 & 
                                                                    n_4659=v_int_232_4724+
                                                                    2 & 
                                                                    0<=m1_4661 & 
                                                                    0<=m2_4664 & 
                                                                    2<=(v_int_232_4724+
                                                                    2) & 
                                                                    v_node_231_4613!=null) & 
                                                                    (2709::n1_4709=v_int_232_4724-
                                                                    1 & 
                                                                    n_4669=v_int_232_4724 & 
                                                                    m_4668=m2_4711+
                                                                    m1_4708+
                                                                    1 & 
                                                                    n_4706=v_int_232_4724 & 
                                                                    (v_int_232_4724-
                                                                    2)<=n2_4712 & 
                                                                    0<=n2_4712 & 
                                                                    n2_4712<v_int_232_4724 & 
                                                                    0<=m1_4708 & 
                                                                    0<=m2_4711 & 
                                                                    q_4571!=null | 
                                                                    n2_4712=v_int_232_4724-
                                                                    1 & 
                                                                    n1_4709=v_int_232_4724-
                                                                    2 & 
                                                                    n_4669=v_int_232_4724 & 
                                                                    m_4668=m2_4711+
                                                                    m1_4708+
                                                                    1 & 
                                                                    n_4706=v_int_232_4724 & 
                                                                    0<=m1_4708 & 
                                                                    0<=m2_4711 & 
                                                                    2<=v_int_232_4724 & 
                                                                    q_4571!=null) & 
                                                                    (2781::n1_4838=v_int_235_5245-
                                                                    1 & 
                                                                    n_4746=v_int_235_5245 & 
                                                                    m_4745=m2_4840+
                                                                    m1_4837+
                                                                    1 & 
                                                                    n_4835=v_int_235_5245 & 
                                                                    (v_int_235_5245-
                                                                    2)<=n2_4841 & 
                                                                    0<=n2_4841 & 
                                                                    n2_4841<v_int_235_5245 & 
                                                                    0<=m1_4837 & 
                                                                    0<=m2_4840 & 
                                                                    p_4660!=null | 
                                                                    n2_4841=v_int_235_5245-
                                                                    1 & 
                                                                    n1_4838=v_int_235_5245-
                                                                    2 & 
                                                                    n_4746=v_int_235_5245 & 
                                                                    m_4745=m2_4840+
                                                                    m1_4837+
                                                                    1 & 
                                                                    n_4835=v_int_235_5245 & 
                                                                    0<=m1_4837 & 
                                                                    0<=m2_4840 & 
                                                                    2<=v_int_235_5245 & 
                                                                    p_4660!=null) & 
                                                                    (2821::n1_4975=v_int_235_5246-
                                                                    1 & 
                                                                    n_4847=v_int_235_5246 & 
                                                                    m_4846=m2_4977+
                                                                    m1_4974+
                                                                    1 & 
                                                                    n_4972=v_int_235_5246 & 
                                                                    (v_int_235_5246-
                                                                    2)<=n2_4978 & 
                                                                    0<=n2_4978 & 
                                                                    n2_4978<v_int_235_5246 & 
                                                                    0<=m1_4974 & 
                                                                    0<=m2_4977 & 
                                                                    q_4663!=null | 
                                                                    n2_4978=v_int_235_5246-
                                                                    1 & 
                                                                    n1_4975=v_int_235_5246-
                                                                    2 & 
                                                                    n_4847=v_int_235_5246 & 
                                                                    m_4846=m2_4977+
                                                                    m1_4974+
                                                                    1 & 
                                                                    n_4972=v_int_235_5246 & 
                                                                    0<=m1_4974 & 
                                                                    0<=m2_4977 & 
                                                                    2<=v_int_235_5246 & 
                                                                    q_4663!=null) & 
                                                                    (3135::n1_5304=n_4835-
                                                                    1 & 
                                                                    n2_5307<n_4835 | 
                                                                    n2_5307=n_4835-
                                                                    1 & 
                                                                    n1_5304<=(n_4835-
                                                                    2)) & 
                                                                    (3135::n1_5304=n_5252-
                                                                    1 & 
                                                                    n2_5307<n_5252 | 
                                                                    n2_5307=n_5252-
                                                                    1 & 
                                                                    n1_5304<=(n_5252-
                                                                    2)) & 
                                                                    (3131::n1_5397=v_int_249_5635-
                                                                    1 & 
                                                                    n_5252=v_int_249_5635 & 
                                                                    m_5251=m2_5399+
                                                                    m1_5396+
                                                                    1 & 
                                                                    n_5394=v_int_249_5635 & 
                                                                    (v_int_249_5635-
                                                                    2)<=n2_5400 & 
                                                                    0<=n2_5400 & 
                                                                    n2_5400<v_int_249_5635 & 
                                                                    0<=m1_5396 & 
                                                                    0<=m2_5399 & 
                                                                    p_4660!=null | 
                                                                    n2_5400=v_int_249_5635-
                                                                    1 & 
                                                                    n1_5397=v_int_249_5635-
                                                                    2 & 
                                                                    n_5252=v_int_249_5635 & 
                                                                    m_5251=m2_5399+
                                                                    m1_5396+
                                                                    1 & 
                                                                    n_5394=v_int_249_5635 & 
                                                                    0<=m1_5396 & 
                                                                    0<=m2_5399 & 
                                                                    2<=v_int_249_5635 & 
                                                                    p_4660!=null) & 
                                                                    (3195::n1_5482=n_4972-
                                                                    1 & 
                                                                    n2_5485<n_4972 | 
                                                                    n2_5485=n_4972-
                                                                    1 & 
                                                                    n1_5482<=(n_4972-
                                                                    2)) & 
                                                                    (3195::n1_5482=n_5406-
                                                                    1 & 
                                                                    n2_5485<n_5406 | 
                                                                    n2_5485=n_5406-
                                                                    1 & 
                                                                    n1_5482<=(n_5406-
                                                                    2)) & 
                                                                    (3191::n1_5609=(1+
                                                                    v_int_249_5635)-
                                                                    1 & 
                                                                    n_5406=1+
                                                                    v_int_249_5635 & 
                                                                    m_5405=m2_5607+
                                                                    m1_5610+
                                                                    1 & 
                                                                    n_5612=1+
                                                                    v_int_249_5635 & 
                                                                    ((1+
                                                                    v_int_249_5635)-
                                                                    2)<=n2_5606 & 
                                                                    0<=n2_5606 & 
                                                                    n2_5606<(1+
                                                                    v_int_249_5635) & 
                                                                    0<=m1_5610 & 
                                                                    0<=m2_5607 & 
                                                                    q_4663!=null | 
                                                                    n2_5606=(1+
                                                                    v_int_249_5635)-
                                                                    1 & 
                                                                    n1_5609=(1+
                                                                    v_int_249_5635)-
                                                                    2 & 
                                                                    n_5406=1+
                                                                    v_int_249_5635 & 
                                                                    m_5405=m2_5607+
                                                                    m1_5610+
                                                                    1 & 
                                                                    n_5612=1+
                                                                    v_int_249_5635 & 
                                                                    0<=m1_5610 & 
                                                                    0<=m2_5607 & 
                                                                    2<=(1+
                                                                    v_int_249_5635) & 
                                                                    q_4663!=null) & 
                                                                    (3392::n1_5721=hr_74'-
                                                                    1 & 
                                                                    n_5675=hr_74' & 
                                                                    m_5674=m2_5723+
                                                                    m1_5720+
                                                                    1 & 
                                                                    n_5718=hr_74' & 
                                                                    (hr_74'-
                                                                    2)<=n2_5724 & 
                                                                    0<=n2_5724 & 
                                                                    n2_5724<hr_74' & 
                                                                    0<=m1_5720 & 
                                                                    0<=m2_5723 & 
                                                                    p_5611!=null | 
                                                                    n2_5724=hr_74'-
                                                                    1 & 
                                                                    n1_5721=hr_74'-
                                                                    2 & 
                                                                    n_5675=hr_74' & 
                                                                    m_5674=m2_5723+
                                                                    m1_5720+
                                                                    1 & 
                                                                    n_5718=hr_74' & 
                                                                    0<=m1_5720 & 
                                                                    0<=m2_5723 & 
                                                                    2<=hr_74' & 
                                                                    p_5611!=null) & 
                                                                    0<=m_5251 & 
                                                                    0!=n1_4607 & 
                                                                    (-1+
                                                                    n1_5482)<=n2_5485 & 
                                                                    0<=m_5405 & 
                                                                    (-1+
                                                                    n1_5304)<=n2_5307 & 
                                                                    0<=m_4846 & 
                                                                    m_5405=1+
                                                                    m1_5481+
                                                                    m2_5484 & 
                                                                    v_int_235_5245<=v_int_235_5246 & 
                                                                    m_5251=1+
                                                                    m1_5303+
                                                                    m2_5306 & 
                                                                    (-1+
                                                                    n2_5485)<=n1_5482 & 
                                                                    0<=n_5675 & 
                                                                    0<=flted_219_4606 & 
                                                                    0<=m_4745 & 
                                                                    k2_70'!=null & 
                                                                    0!=n & 
                                                                    m=1+
                                                                    m1_4569+
                                                                    m2_4572 & 
                                                                    (-1+
                                                                    n1_4570)<=n2_4573 & 
                                                                    0<=m & 
                                                                    0<=n2_4573 & 
                                                                    0<=n_5252 & 
                                                                    0<=n_5406 & 
                                                                    n_4587<=n1_4607 & 
                                                                    (-1+
                                                                    n2_4573)<=n1_4570 & 
                                                                    (-1+
                                                                    n1_4607)<=n_4587 & 
                                                                    0<=m1_4569 & 
                                                                    0<=n & 
                                                                    0<=n1_4607 & 
                                                                    0!=m & 
                                                                    null!=v_node_231_4613 & 
                                                                    0<=n_4746 & 
                                                                    (-1+
                                                                    n2_5307)<=n1_5304 & 
                                                                    p_4660!=null & 
                                                                    0!=flted_219_4606 & 
                                                                    0<=m2_4572 & 
                                                                    0<=n1_4570 & 
                                                                    0<=m_5674 & 
                                                                    0<=n_4847 & 
                                                                    -1+
                                                                    flted_219_4606=m_4586]
                                                                    [v_bool_249_836']
                                                                    [Anon_5479=Anon_4971]
                                                                    [p_5480=p_4973]
                                                                    [q_5483=q_4976]
                                                                    [Anon_5301=Anon_4834]
                                                                    [p_5302=p_4836]
                                                                    [q_5305=q_4839]
                                                                    [!(v_bool_235_837')]
                                                                    [p_4568=tmp_69']
                                                                    [v_bool_228_1007']
                                                                    [a=a' & 
                                                                    a'<=Anon_4567]
                                                                    [x=x' & 
                                                                    x'!=null]
                                                                    [tmp_71'=null]
                                                                    [!(v_bool_224_1008')]
                                                                    [v_bool_232_839']
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure Call:avl_msh.ss:300: 23: 
Verification Context:(Line:219,Col:10)
Proving precondition in method height$node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[m_6388; 
                  n_6389](ex)v_node_300_911'::avl<m_6388,n_6389>@I[Orig][LHSCase]@ rem br[{651,650}]&
                  (([0<=m_6388][0<=n_6389]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(
                              ([null=v_node_300_911'][0=m_6388 & 0<=m_6388]
                               [0=n_6389 & 0<=n_6389][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1859,n_1860,p_1861,m1_1862,
                                 n1_1863,q_1864,m2_1865,
                                 n2_1866: v_node_300_911'::node<Anon_1859,n_1860,p_1861,q_1864>@I[Orig][] * 
                                 p_1861::avl<m1_1862,n1_1863>@I[Orig]@ rem br[{651,650}] * 
                                 q_1864::avl<m2_1865,n2_1866>@I[Orig]@ rem br[{651,650}]&
                                 (
                                 ([(n1_1863=res-1 & n_6389=res & 
                                    m_6388=m2_1865+m1_1862+1 & n_1860=res & 
                                    (res-2)<=n2_1866 & 0<=n2_1866 & 
                                    n2_1866<res & 0<=m1_1862 & 0<=m2_1865 & 
                                    v_node_300_911'!=null | n2_1866=res-1 & 
                                    n1_1863=res-2 & n_6389=res & 
                                    m_6388=m2_1865+m1_1862+1 & n_1860=res & 
                                    0<=m1_1862 & 0<=m2_1865 & 2<=res & 
                                    v_node_300_911'!=null) & 0<=m_6388 & 
                                    0<=n_6389]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
Current States: [ q_5855::node<Anon_6026,n_6027,p_6028,q_6031>@I[Orig][] * p_6028::avl<m1_6029,n1_6030>@I[Orig]@ rem br[{651,650}] * q_6031::avl<m2_6032,n2_6033>@I[Orig]@ rem br[{651,650}] * p_5852::node<Anon_6287,n_6288,p_6289,q_6292>@I[Orig][] * p_6289::avl<m1_6290,n1_6291>@I[Orig]@ rem br[{651,650}] * q_6292::avl<m2_6293,n2_6294>@I[Orig]@ rem br[{651,650}] * k1_68'::node<val_293_6304,height_293_6305,x,right_293_6306>@M[Orig][] * p_4568::node<Anon_6363,n_6364,p_6365,q_6368>@I[Orig][] * p_6365::avl<m1_6366,n1_6367>@I[Orig]@ rem br[{651,650}] * q_6368::avl<m2_6369,n2_6370>@I[Orig]@ rem br[{651,650}] * x'::node<Anon_4567,h_72',p_4568,p_5852>@M[Orig][]&(([
                                                                    v_node_300_911'=right_293_6306]
                                                                    [n_6310=n_5898 & 
                                                                    m2_6318=m2_5903 & 
                                                                    n2_6319=n2_5904 & 
                                                                    m1_6315=m1_5900 & 
                                                                    n1_6316=n1_5901 & 
                                                                    n_6216=n_6148 & 
                                                                    m2_6235=m2_6153 & 
                                                                    n2_6236=n2_6154 & 
                                                                    m1_6232=m1_6150 & 
                                                                    n1_6233=n1_6151 & 
                                                                    m_6038=m1_5853 & 
                                                                    n_6039=n1_5854 & 
                                                                    m_5937=m2_5856 & 
                                                                    n_5938=n2_5857 & 
                                                                    v_node_285_5805=k1_68' & 
                                                                    n_5779=n2_4573 & 
                                                                    n_4566=n & 
                                                                    n1_5799=n_5809 & 
                                                                    m_5778=m2_4572 & 
                                                                    flted_219_5798=m_5808 & 
                                                                    n1_4570=n_5861 & 
                                                                    m1_4569=m_5860 & 
                                                                    (2654::n1_4570=n-
                                                                    1 & 
                                                                    n2_4573<n | 
                                                                    n2_4573=n-
                                                                    1 & 
                                                                    n1_4570<=(n-
                                                                    2)) & 
                                                                    (3529::n1_5854=(v_int_286_5916+
                                                                    2)-1 & 
                                                                    n_5809=v_int_286_5916+
                                                                    2 & 
                                                                    m_5808=m2_5856+
                                                                    m1_5853+
                                                                    1 & 
                                                                    n_5851=v_int_286_5916+
                                                                    2 & 
                                                                    ((v_int_286_5916+
                                                                    2)-
                                                                    2)<=n2_5857 & 
                                                                    0<=n2_5857 & 
                                                                    n2_5857<(v_int_286_5916+
                                                                    2) & 
                                                                    0<=m1_5853 & 
                                                                    0<=m2_5856 & 
                                                                    v_node_285_5805!=null | 
                                                                    n2_5857=(v_int_286_5916+
                                                                    2)-1 & 
                                                                    n1_5854=(v_int_286_5916+
                                                                    2)-2 & 
                                                                    n_5809=v_int_286_5916+
                                                                    2 & 
                                                                    m_5808=m2_5856+
                                                                    m1_5853+
                                                                    1 & 
                                                                    n_5851=v_int_286_5916+
                                                                    2 & 
                                                                    0<=m1_5853 & 
                                                                    0<=m2_5856 & 
                                                                    2<=(v_int_286_5916+
                                                                    2) & 
                                                                    v_node_285_5805!=null) & 
                                                                    (3545::n1_5901=v_int_286_5916-
                                                                    1 & 
                                                                    n_5861=v_int_286_5916 & 
                                                                    m_5860=m2_5903+
                                                                    m1_5900+
                                                                    1 & 
                                                                    n_5898=v_int_286_5916 & 
                                                                    (v_int_286_5916-
                                                                    2)<=n2_5904 & 
                                                                    0<=n2_5904 & 
                                                                    n2_5904<v_int_286_5916 & 
                                                                    0<=m1_5900 & 
                                                                    0<=m2_5903 & 
                                                                    p_4568!=null | 
                                                                    n2_5904=v_int_286_5916-
                                                                    1 & 
                                                                    n1_5901=v_int_286_5916-
                                                                    2 & 
                                                                    n_5861=v_int_286_5916 & 
                                                                    m_5860=m2_5903+
                                                                    m1_5900+
                                                                    1 & 
                                                                    n_5898=v_int_286_5916 & 
                                                                    0<=m1_5900 & 
                                                                    0<=m2_5903 & 
                                                                    2<=v_int_286_5916 & 
                                                                    p_4568!=null) & 
                                                                    (3617::n1_6030=v_int_289_6194-
                                                                    1 & 
                                                                    n_5938=v_int_289_6194 & 
                                                                    m_5937=m2_6032+
                                                                    m1_6029+
                                                                    1 & 
                                                                    n_6027=v_int_289_6194 & 
                                                                    (v_int_289_6194-
                                                                    2)<=n2_6033 & 
                                                                    0<=n2_6033 & 
                                                                    n2_6033<v_int_289_6194 & 
                                                                    0<=m1_6029 & 
                                                                    0<=m2_6032 & 
                                                                    q_5855!=null | 
                                                                    n2_6033=v_int_289_6194-
                                                                    1 & 
                                                                    n1_6030=v_int_289_6194-
                                                                    2 & 
                                                                    n_5938=v_int_289_6194 & 
                                                                    m_5937=m2_6032+
                                                                    m1_6029+
                                                                    1 & 
                                                                    n_6027=v_int_289_6194 & 
                                                                    0<=m1_6029 & 
                                                                    0<=m2_6032 & 
                                                                    2<=v_int_289_6194 & 
                                                                    q_5855!=null) & 
                                                                    (3657::n1_6151=v_int_289_6195-
                                                                    1 & 
                                                                    n_6039=v_int_289_6195 & 
                                                                    m_6038=m2_6153+
                                                                    m1_6150+
                                                                    1 & 
                                                                    n_6148=v_int_289_6195 & 
                                                                    (v_int_289_6195-
                                                                    2)<=n2_6154 & 
                                                                    0<=n2_6154 & 
                                                                    n2_6154<v_int_289_6195 & 
                                                                    0<=m1_6150 & 
                                                                    0<=m2_6153 & 
                                                                    p_5852!=null | 
                                                                    n2_6154=v_int_289_6195-
                                                                    1 & 
                                                                    n1_6151=v_int_289_6195-
                                                                    2 & 
                                                                    n_6039=v_int_289_6195 & 
                                                                    m_6038=m2_6153+
                                                                    m1_6150+
                                                                    1 & 
                                                                    n_6148=v_int_289_6195 & 
                                                                    0<=m1_6150 & 
                                                                    0<=m2_6153 & 
                                                                    2<=v_int_289_6195 & 
                                                                    p_5852!=null) & 
                                                                    (3783::n1_6233=n_6148-
                                                                    1 & 
                                                                    n2_6236<n_6148 | 
                                                                    n2_6236=n_6148-
                                                                    1 & 
                                                                    n1_6233<=(n_6148-
                                                                    2)) & 
                                                                    (3783::n1_6233=n_6216-
                                                                    1 & 
                                                                    n2_6236<n_6216 | 
                                                                    n2_6236=n_6216-
                                                                    1 & 
                                                                    n1_6233<=(n_6216-
                                                                    2)) & 
                                                                    (3779::n1_6291=hr_74'-
                                                                    1 & 
                                                                    n_6216=hr_74' & 
                                                                    m_6215=m2_6293+
                                                                    m1_6290+
                                                                    1 & 
                                                                    n_6288=hr_74' & 
                                                                    (hr_74'-
                                                                    2)<=n2_6294 & 
                                                                    0<=n2_6294 & 
                                                                    n2_6294<hr_74' & 
                                                                    0<=m1_6290 & 
                                                                    0<=m2_6293 & 
                                                                    p_5852!=null | 
                                                                    n2_6294=hr_74'-
                                                                    1 & 
                                                                    n1_6291=hr_74'-
                                                                    2 & 
                                                                    n_6216=hr_74' & 
                                                                    m_6215=m2_6293+
                                                                    m1_6290+
                                                                    1 & 
                                                                    n_6288=hr_74' & 
                                                                    0<=m1_6290 & 
                                                                    0<=m2_6293 & 
                                                                    2<=hr_74' & 
                                                                    p_5852!=null) & 
                                                                    (3838::n1_6316=n_5898-
                                                                    1 & 
                                                                    n2_6319<n_5898 | 
                                                                    n2_6319=n_5898-
                                                                    1 & 
                                                                    n1_6316<=(n_5898-
                                                                    2)) & 
                                                                    (3838::n1_6316=n_6310-
                                                                    1 & 
                                                                    n2_6319<n_6310 | 
                                                                    n2_6319=n_6310-
                                                                    1 & 
                                                                    n1_6316<=(n_6310-
                                                                    2)) & 
                                                                    (3834::n1_6367=hl_73'-
                                                                    1 & 
                                                                    n_6310=hl_73' & 
                                                                    m_6309=m2_6369+
                                                                    m1_6366+
                                                                    1 & 
                                                                    n_6364=hl_73' & 
                                                                    (hl_73'-
                                                                    2)<=n2_6370 & 
                                                                    0<=n2_6370 & 
                                                                    n2_6370<hl_73' & 
                                                                    0<=m1_6366 & 
                                                                    0<=m2_6369 & 
                                                                    p_4568!=null | 
                                                                    n2_6370=hl_73'-
                                                                    1 & 
                                                                    n1_6367=hl_73'-
                                                                    2 & 
                                                                    n_6310=hl_73' & 
                                                                    m_6309=m2_6369+
                                                                    m1_6366+
                                                                    1 & 
                                                                    n_6364=hl_73' & 
                                                                    0<=m1_6366 & 
                                                                    0<=m2_6369 & 
                                                                    2<=hl_73' & 
                                                                    p_4568!=null) & 
                                                                    h_6382=max(hr_74',
                                                                    hl_73') & 
                                                                    0<=n_6310 & 
                                                                    0<=flted_219_5798 & 
                                                                    0<=m_6038 & 
                                                                    0<=n1_5799 & 
                                                                    (1+
                                                                    v_int_289_6195)<=v_int_289_6194 & 
                                                                    (-1+
                                                                    n2_6236)<=n1_6233 & 
                                                                    h_72'=h_6382+
                                                                    1 & m=1+
                                                                    m1_4569+
                                                                    m2_4572 & 
                                                                    0<=n_6039 & 
                                                                    0<=m_6215 & 
                                                                    -1+
                                                                    flted_219_5798=m_5778 & 
                                                                    m_6215=1+
                                                                    m1_6232+
                                                                    m2_6235 & 
                                                                    (-1+
                                                                    n1_4570)<=n2_4573 & 
                                                                    0<=m_5937 & 
                                                                    n_5779<=n1_5799 & 
                                                                    m_6309=1+
                                                                    m1_6315+
                                                                    m2_6318 & 
                                                                    (-1+
                                                                    n1_6316)<=n2_6319 & 
                                                                    0<=m1_4569 & 
                                                                    0!=n & 
                                                                    (-1+
                                                                    n2_4573)<=n1_4570 & 
                                                                    0<=m2_4572 & 
                                                                    0<=n_6216 & 
                                                                    0<=m & 
                                                                    null!=v_node_285_5805 & 
                                                                    p_4568!=null & 
                                                                    (-1+
                                                                    n2_6319)<=n1_6316 & 
                                                                    0!=flted_219_5798 & 
                                                                    0!=m & 
                                                                    0!=n1_5799 & 
                                                                    0<=n2_4573 & 
                                                                    p_5852!=null & 
                                                                    (-1+
                                                                    n1_6233)<=n2_6236 & 
                                                                    0<=n & 
                                                                    0<=m_6309 & 
                                                                    0<=n1_4570 & 
                                                                    (-1+
                                                                    n1_5799)<=n_5779 & 
                                                                    0<=n_5938]
                                                                    [Anon_6313=Anon_5897]
                                                                    [p_5899=p_6314]
                                                                    [q_5902=q_6317]
                                                                    [v_bool_286_1006']
                                                                    [!(v_bool_224_1008')]
                                                                    [null=tmp_71']
                                                                    [x=x' & 
                                                                    x'!=null]
                                                                    [a'=a & 
                                                                    (1+
                                                                    Anon_4567)<=a']
                                                                    [!(v_bool_228_1007')]
                                                                    [tmp_69'=q_4571]
                                                                    [v_bool_289_1004']
                                                                    [q_6152=q_6234]
                                                                    [p_6149=p_6231]
                                                                    [Anon_6230=Anon_6147]
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure Call:avl_msh.ss:317: 28: 
Verification Context:(Line:219,Col:10)
Proving precondition in method height$node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[m_6908; 
                  n_6909](ex)v_node_317_968'::avl<m_6908,n_6909>@I[Orig][LHSCase]@ rem br[{651,650}]&
                  (([0<=m_6908][0<=n_6909]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(
                              ([null=v_node_317_968'][0=m_6908 & 0<=m_6908]
                               [0=n_6909 & 0<=n_6909][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(Anon_1859,n_1860,p_1861,m1_1862,
                                 n1_1863,q_1864,m2_1865,
                                 n2_1866: v_node_317_968'::node<Anon_1859,n_1860,p_1861,q_1864>@I[Orig][] * 
                                 p_1861::avl<m1_1862,n1_1863>@I[Orig]@ rem br[{651,650}] * 
                                 q_1864::avl<m2_1865,n2_1866>@I[Orig]@ rem br[{651,650}]&
                                 (
                                 ([(n1_1863=res-1 & n_6909=res & 
                                    m_6908=m2_1865+m1_1862+1 & n_1860=res & 
                                    (res-2)<=n2_1866 & 0<=n2_1866 & 
                                    n2_1866<res & 0<=m1_1862 & 0<=m2_1865 & 
                                    v_node_317_968'!=null | n2_1866=res-1 & 
                                    n1_1863=res-2 & n_6909=res & 
                                    m_6908=m2_1865+m1_1862+1 & n_1860=res & 
                                    0<=m1_1862 & 0<=m2_1865 & 2<=res & 
                                    v_node_317_968'!=null) & 0<=m_6908 & 
                                    0<=n_6909]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
Current States: [ p_4568::node<Anon_5897,n_5898,p_5899,q_5902>@I[Orig][] * p_5899::avl<m1_5900,n1_5901>@I[Orig]@ rem br[{651,650}] * q_5902::avl<m2_5903,n2_5904>@I[Orig]@ rem br[{651,650}] * q_6623::avl<m2_6622,n2_6621>@I[Orig]@ rem br[{651,650}] * q_5855::node<Anon_6766,n_6767,p_6768,q_6771>@I[Orig][] * p_6768::avl<m1_6769,n1_6770>@I[Orig]@ rem br[{651,650}] * q_6771::avl<m2_6772,n2_6773>@I[Orig]@ rem br[{651,650}] * x'::node<Anon_4567,n_4566,p_4568,p_6626>@M[Orig][] * k1_68'::node<val_314_6838,height_314_6839,q_6623,right_314_6840>@M[Orig][] * p_6626::node<Anon_6886,n_6887,p_6888,q_6891>@I[Orig][] * p_6888::avl<m1_6889,n1_6890>@I[Orig]@ rem br[{651,650}] * q_6891::avl<m2_6892,n2_6893>@I[Orig]@ rem br[{651,650}] * k2_70'::node<val_316_6903,height_316_6904,x,right_316_6905>@M[Orig][]&(([
                                                                    v_node_317_968'=right_316_6905]
                                                                    [m_6843=m1_6625 & 
                                                                    n_6844=n1_6624 & 
                                                                    p_5852=k2_70' & 
                                                                    n_6641=n_6027 & 
                                                                    m2_6695=m2_6032 & 
                                                                    n2_6696=n2_6033 & 
                                                                    m1_6692=m1_6029 & 
                                                                    n1_6693=n1_6030 & 
                                                                    m_5860=m1_4569 & 
                                                                    n_5861=n1_4570 & 
                                                                    m_5808=flted_219_5798 & 
                                                                    m2_4572=m_5778 & 
                                                                    n_5809=n1_5799 & 
                                                                    n=n_4566 & 
                                                                    n2_4573=n_5779 & 
                                                                    k1_68'=v_node_285_5805 & 
                                                                    n2_5857=n_5938 & 
                                                                    m2_5856=m_5937 & 
                                                                    n1_5854=n_6039 & 
                                                                    m1_5853=m_6038 & 
                                                                    n1_6167=n1_6497 & 
                                                                    m1_6166=m1_6496 & 
                                                                    n2_6170=n2_6500 & 
                                                                    m2_6169=m2_6499 & 
                                                                    n_6164=n_6421 & 
                                                                    (2654::n1_4570=n-
                                                                    1 & 
                                                                    n2_4573<n | 
                                                                    n2_4573=n-
                                                                    1 & 
                                                                    n1_4570<=(n-
                                                                    2)) & 
                                                                    (3529::n1_5854=(v_int_286_5916+
                                                                    2)-1 & 
                                                                    n_5809=v_int_286_5916+
                                                                    2 & 
                                                                    m_5808=m2_5856+
                                                                    m1_5853+
                                                                    1 & 
                                                                    n_5851=v_int_286_5916+
                                                                    2 & 
                                                                    ((v_int_286_5916+
                                                                    2)-
                                                                    2)<=n2_5857 & 
                                                                    0<=n2_5857 & 
                                                                    n2_5857<(v_int_286_5916+
                                                                    2) & 
                                                                    0<=m1_5853 & 
                                                                    0<=m2_5856 & 
                                                                    v_node_285_5805!=null | 
                                                                    n2_5857=(v_int_286_5916+
                                                                    2)-1 & 
                                                                    n1_5854=(v_int_286_5916+
                                                                    2)-2 & 
                                                                    n_5809=v_int_286_5916+
                                                                    2 & 
                                                                    m_5808=m2_5856+
                                                                    m1_5853+
                                                                    1 & 
                                                                    n_5851=v_int_286_5916+
                                                                    2 & 
                                                                    0<=m1_5853 & 
                                                                    0<=m2_5856 & 
                                                                    2<=(v_int_286_5916+
                                                                    2) & 
                                                                    v_node_285_5805!=null) & 
                                                                    (3545::n1_5901=v_int_286_5916-
                                                                    1 & 
                                                                    n_5861=v_int_286_5916 & 
                                                                    m_5860=m2_5903+
                                                                    m1_5900+
                                                                    1 & 
                                                                    n_5898=v_int_286_5916 & 
                                                                    (v_int_286_5916-
                                                                    2)<=n2_5904 & 
                                                                    0<=n2_5904 & 
                                                                    n2_5904<v_int_286_5916 & 
                                                                    0<=m1_5900 & 
                                                                    0<=m2_5903 & 
                                                                    p_4568!=null | 
                                                                    n2_5904=v_int_286_5916-
                                                                    1 & 
                                                                    n1_5901=v_int_286_5916-
                                                                    2 & 
                                                                    n_5861=v_int_286_5916 & 
                                                                    m_5860=m2_5903+
                                                                    m1_5900+
                                                                    1 & 
                                                                    n_5898=v_int_286_5916 & 
                                                                    0<=m1_5900 & 
                                                                    0<=m2_5903 & 
                                                                    2<=v_int_286_5916 & 
                                                                    p_4568!=null) & 
                                                                    (3617::n1_6030=v_int_289_6414-
                                                                    1 & 
                                                                    n_5938=v_int_289_6414 & 
                                                                    m_5937=m2_6032+
                                                                    m1_6029+
                                                                    1 & 
                                                                    n_6027=v_int_289_6414 & 
                                                                    (v_int_289_6414-
                                                                    2)<=n2_6033 & 
                                                                    0<=n2_6033 & 
                                                                    n2_6033<v_int_289_6414 & 
                                                                    0<=m1_6029 & 
                                                                    0<=m2_6032 & 
                                                                    q_5855!=null | 
                                                                    n2_6033=v_int_289_6414-
                                                                    1 & 
                                                                    n1_6030=v_int_289_6414-
                                                                    2 & 
                                                                    n_5938=v_int_289_6414 & 
                                                                    m_5937=m2_6032+
                                                                    m1_6029+
                                                                    1 & 
                                                                    n_6027=v_int_289_6414 & 
                                                                    0<=m1_6029 & 
                                                                    0<=m2_6032 & 
                                                                    2<=v_int_289_6414 & 
                                                                    q_5855!=null) & 
                                                                    (3657::n1_6167=v_int_289_6415-
                                                                    1 & 
                                                                    n_6039=v_int_289_6415 & 
                                                                    m_6038=m2_6169+
                                                                    m1_6166+
                                                                    1 & 
                                                                    n_6164=v_int_289_6415 & 
                                                                    (v_int_289_6415-
                                                                    2)<=n2_6170 & 
                                                                    0<=n2_6170 & 
                                                                    n2_6170<v_int_289_6415 & 
                                                                    0<=m1_6166 & 
                                                                    0<=m2_6169 & 
                                                                    p_5852!=null | 
                                                                    n2_6170=v_int_289_6415-
                                                                    1 & 
                                                                    n1_6167=v_int_289_6415-
                                                                    2 & 
                                                                    n_6039=v_int_289_6415 & 
                                                                    m_6038=m2_6169+
                                                                    m1_6166+
                                                                    1 & 
                                                                    n_6164=v_int_289_6415 & 
                                                                    0<=m1_6166 & 
                                                                    0<=m2_6169 & 
                                                                    2<=v_int_289_6415 & 
                                                                    p_5852!=null) & 
                                                                    (3953::n1_6497=n_6164-
                                                                    1 & 
                                                                    n2_6500<n_6164 | 
                                                                    n2_6500=n_6164-
                                                                    1 & 
                                                                    n1_6497<=(n_6164-
                                                                    2)) & 
                                                                    (3953::n1_6497=n_6421-
                                                                    1 & 
                                                                    n2_6500<n_6421 | 
                                                                    n2_6500=n_6421-
                                                                    1 & 
                                                                    n1_6497<=(n_6421-
                                                                    2)) & 
                                                                    (3949::n1_6624=(1+
                                                                    v_int_309_6804)-
                                                                    1 & 
                                                                    n_6421=1+
                                                                    v_int_309_6804 & 
                                                                    m_6420=m2_6622+
                                                                    m1_6625+
                                                                    1 & 
                                                                    n_6627=1+
                                                                    v_int_309_6804 & 
                                                                    ((1+
                                                                    v_int_309_6804)-
                                                                    2)<=n2_6621 & 
                                                                    0<=n2_6621 & 
                                                                    n2_6621<(1+
                                                                    v_int_309_6804) & 
                                                                    0<=m1_6625 & 
                                                                    0<=m2_6622 & 
                                                                    p_5852!=null | 
                                                                    n2_6621=(1+
                                                                    v_int_309_6804)-
                                                                    1 & 
                                                                    n1_6624=(1+
                                                                    v_int_309_6804)-
                                                                    2 & 
                                                                    n_6421=1+
                                                                    v_int_309_6804 & 
                                                                    m_6420=m2_6622+
                                                                    m1_6625+
                                                                    1 & 
                                                                    n_6627=1+
                                                                    v_int_309_6804 & 
                                                                    0<=m1_6625 & 
                                                                    0<=m2_6622 & 
                                                                    2<=(1+
                                                                    v_int_309_6804) & 
                                                                    p_5852!=null) & 
                                                                    (4041::n1_6693=n_6027-
                                                                    1 & 
                                                                    n2_6696<n_6027 | 
                                                                    n2_6696=n_6027-
                                                                    1 & 
                                                                    n1_6693<=(n_6027-
                                                                    2)) & 
                                                                    (4041::n1_6693=n_6641-
                                                                    1 & 
                                                                    n2_6696<n_6641 | 
                                                                    n2_6696=n_6641-
                                                                    1 & 
                                                                    n1_6693<=(n_6641-
                                                                    2)) & 
                                                                    (4037::n1_6770=v_int_309_6804-
                                                                    1 & 
                                                                    n_6641=v_int_309_6804 & 
                                                                    m_6640=m2_6772+
                                                                    m1_6769+
                                                                    1 & 
                                                                    n_6767=v_int_309_6804 & 
                                                                    (v_int_309_6804-
                                                                    2)<=n2_6773 & 
                                                                    0<=n2_6773 & 
                                                                    n2_6773<v_int_309_6804 & 
                                                                    0<=m1_6769 & 
                                                                    0<=m2_6772 & 
                                                                    q_5855!=null | 
                                                                    n2_6773=v_int_309_6804-
                                                                    1 & 
                                                                    n1_6770=v_int_309_6804-
                                                                    2 & 
                                                                    n_6641=v_int_309_6804 & 
                                                                    m_6640=m2_6772+
                                                                    m1_6769+
                                                                    1 & 
                                                                    n_6767=v_int_309_6804 & 
                                                                    0<=m1_6769 & 
                                                                    0<=m2_6772 & 
                                                                    2<=v_int_309_6804 & 
                                                                    q_5855!=null) & 
                                                                    (4210::n1_6890=hr_74'-
                                                                    1 & 
                                                                    n_6844=hr_74' & 
                                                                    m_6843=m2_6892+
                                                                    m1_6889+
                                                                    1 & 
                                                                    n_6887=hr_74' & 
                                                                    (hr_74'-
                                                                    2)<=n2_6893 & 
                                                                    0<=n2_6893 & 
                                                                    n2_6893<hr_74' & 
                                                                    0<=m1_6889 & 
                                                                    0<=m2_6892 & 
                                                                    p_6626!=null | 
                                                                    n2_6893=hr_74'-
                                                                    1 & 
                                                                    n1_6890=hr_74'-
                                                                    2 & 
                                                                    n_6844=hr_74' & 
                                                                    m_6843=m2_6892+
                                                                    m1_6889+
                                                                    1 & 
                                                                    n_6887=hr_74' & 
                                                                    0<=m1_6889 & 
                                                                    0<=m2_6892 & 
                                                                    2<=hr_74' & 
                                                                    p_6626!=null) & 
                                                                    0<=n1_5799 & 
                                                                    0<=n_6844 & 
                                                                    (-1+
                                                                    n1_6693)<=n2_6696 & 
                                                                    0!=n1_5799 & 
                                                                    n_5779<=n1_5799 & 
                                                                    0!=flted_219_5798 & 
                                                                    null!=v_node_285_5805 & 
                                                                    m=1+
                                                                    m1_4569+
                                                                    m2_4572 & 
                                                                    k2_70'!=null & 
                                                                    0<=n1_4570 & 
                                                                    0<=m_6038 & 
                                                                    (-1+
                                                                    n1_6497)<=n2_6500 & 
                                                                    m_6640=1+
                                                                    m1_6692+
                                                                    m2_6695 & 
                                                                    0<=flted_219_5798 & 
                                                                    0<=m_6843 & 
                                                                    (-1+
                                                                    n1_5799)<=n_5779 & 
                                                                    (-1+
                                                                    n1_4570)<=n2_4573 & 
                                                                    0<=m2_4572 & 
                                                                    0<=m_6420 & 
                                                                    0!=m & 
                                                                    0<=m_6640 & 
                                                                    (-1+
                                                                    n2_6500)<=n1_6497 & 
                                                                    0<=m & 
                                                                    0<=n_6641 & 
                                                                    0<=n_6039 & 
                                                                    -1+
                                                                    flted_219_5798=m_5778 & 
                                                                    0!=n & 
                                                                    0<=m_5937 & 
                                                                    0<=n_5938 & 
                                                                    0<=n_6421 & 
                                                                    0<=n2_4573 & 
                                                                    0<=m1_4569 & 
                                                                    (-1+
                                                                    n2_4573)<=n1_4570 & 
                                                                    (-1+
                                                                    n2_6696)<=n1_6693 & 
                                                                    0<=n & 
                                                                    q_5855!=null & 
                                                                    m_6420=1+
                                                                    m1_6496+
                                                                    m2_6499 & 
                                                                    v_int_289_6414<=v_int_289_6415]
                                                                    [v_bool_309_1003']
                                                                    [Anon_6494=Anon_6163]
                                                                    [p_6495=p_6165]
                                                                    [q_6498=q_6168]
                                                                    [!(v_bool_289_1004')]
                                                                    [q_4571=tmp_69']
                                                                    [!(v_bool_228_1007')]
                                                                    [a=a' & 
                                                                    (1+
                                                                    Anon_4567)<=a']
                                                                    [x=x' & 
                                                                    x'!=null]
                                                                    [tmp_71'=null]
                                                                    [!(v_bool_224_1008')]
                                                                    [v_bool_286_1006']
                                                                    [q_6031=q_6694]
                                                                    [p_6028=p_6691]
                                                                    [Anon_6690=Anon_6026]
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure insert_inline$node~int result FAIL-1

Checking procedure merge$node~node... 
!!! REL :  MRG1(h2,h3)
!!! POST:  h2>=0 & h2=h3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG1,t1,t2]
              ECase case {
                     t1=null -> ((None,[]),EBase exists (Expl)(Impl)[s2; 
                                                 h2](ex)t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                 (([0<=s2][0<=h2]))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 153::
                                                             EXISTS(s2_63,
                                                             h3: res::avl<s2_63,h3>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                             (
                                                             ([0<=h3 & 
                                                                MRG1(h2,h3)]
                                                              [s2=s2_63 & 
                                                                0<=s2_63]
                                                              ))&
                                                             {FLOW,(20,21)=__norm}))
                     ;
                     t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; 
                                                  h1; s2; 
                                                  h2](ex)t1::avl<s1,h1>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                                                  t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                  (
                                                  ([0<=s1][0<=h1][0<=s2]
                                                   [0<=h2]))&
                                                  {FLOW,(20,21)=__norm}
                                                    EBase true&MayLoop&
                                                          {FLOW,(1,23)=__flow}
                                                            EAssume 154::
                                                              EXISTS(flted_449_62,
                                                              Anon_17: 
                                                              res::avl<flted_449_62,Anon_17>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                              (
                                                              ([0<=flted_449_62 & 
                                                                 flted_449_62=s1+
                                                                 s2]
                                                               [0<=Anon_17]))&
                                                              {FLOW,(20,21)=__norm}))
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   t1=null -> ((None,[]),EBase exists (Expl)(Impl)[s2; 
                                               h2](ex)t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                               (([0<=s2][0<=h2]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 153::
                                                           EXISTS(s2_7105,
                                                           h3_7106: res::avl<s2_7105,h3_7106>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                           (
                                                           ([h2=h3_7106 & 
                                                              0<=h2]
                                                            [s2=s2_7105 & 
                                                              0<=s2]
                                                            [null=t1]))&
                                                           {FLOW,(20,21)=__norm}))
                   ;
                   t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; h1; 
                                                s2; 
                                                h2](ex)t1::avl<s1,h1>@M[Orig][LHSCase]@ rem br[{651,650}] * 
                                                t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                (
                                                ([0<=s1][0<=h1][0<=s2][
                                                 0<=h2]))&
                                                {FLOW,(20,21)=__norm}
                                                  EBase true&(([MayLoop]))&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 154::
                                                            EXISTS(flted_449_7107,
                                                            Anon_7108: 
                                                            res::avl<flted_449_7107,Anon_7108>@M[Orig][LHSCase]@ rem br[{651,650}]&
                                                            (
                                                            ([0<=flted_449_7107 & 
                                                               0<=s1 & 
                                                               flted_449_7107=s1+
                                                               s2 & 0<=s2]
                                                             [0<=Anon_7108]
                                                             [0<=h2][
                                                             0<=h1][t1!=null]
                                                             ))&
                                                            {FLOW,(20,21)=__norm}))
                   
                   })
!!! NEW RELS:[ (h2=h3 & 0<=h3) --> MRG1(h2,h3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge$node~node SUCCESS

Termination checking result:

Stop Omega... 4054 invocations 
20 false contexts at: ( (457,17)  (457,24)  (461,3)  (461,22)  (461,10)  (460,15)  (460,27)  (460,8)  (459,14)  (459,25)  (459,8)  (459,3)  (340,12)  (336,20)  (280,14)  (276,20)  (211,14)  (207,22)  (190,12)  (186,20) )

Total verification time: 143.07 second(s)
	Time spent in main process: 10.75 second(s)
	Time spent in child processes: 132.32 second(s)
