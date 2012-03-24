
Processing file "rb_msh.ss"
Parsing rb_msh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure case_2$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                    bha](ex)EXISTS(bha_621,bha_622,bha_623,flted_45_617,
                    flted_45_618,flted_45_619,
                    flted_45_620: a::rb<na,flted_45_620,bha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_45_619,bha_621>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_45_618,bha_622>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    d::rb<nd,flted_45_617,bha_623>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_45_620][0=flted_45_619][0=flted_45_618]
                     [0=flted_45_617]
                     [bha=bha_623 & bha=bha_622 & bha=bha_621 & 1<=bha_623]
                     [0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(flted_46_615,flted_46_616,
                                bha1: res::rb<flted_46_616,flted_46_615,bha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_46_616 & flted_46_616=3+na+nb+nc+
                                   nd]
                                 [0=flted_46_615][1<=bha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                  bha](ex)a::rb<na,flted_45_620,bha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_45_619,bha_621>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_45_618,bha_622>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  d::rb<nd,flted_45_617,bha_623>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([bha_622=bha & bha_622=bha_623 & bha_622=bha_621 & 
                     1<=bha_622]
                   [0<=na][0<=nb][0<=nc][0<=nd][0=flted_45_620]
                   [0=flted_45_619][0=flted_45_618][0=flted_45_617]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(flted_46_4250,flted_46_4251,
                              bha1_4252: res::rb<flted_46_4250,flted_46_4251,bha1_4252>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([flted_46_4250=3+na+nb+nc+nd & 0<=nb & 
                                 0<=nc & 0<=nd & 0<=na]
                               [res!=null][-1+bha1_4252=bha & 1<=bha]
                               [0=flted_46_4251][1<=bha_623]
                               [0<=flted_45_617 & flted_45_617<=1]
                               [1<=bha_622]
                               [0<=flted_45_618 & flted_45_618<=1]
                               [1<=bha_621]
                               [0<=flted_45_619 & flted_45_619<=1]
                               [0<=flted_45_620 & flted_45_620<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                    bha](ex)EXISTS(bha_561,bha_562,bha_563,flted_86_557,
                    flted_86_558,flted_86_559,
                    flted_86_560: a::rb<na,flted_86_560,bha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_86_559,bha_561>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_86_558,bha_562>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    d::rb<nd,flted_86_557,bha_563>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_86_560][0=flted_86_559][0=flted_86_558]
                     [0=flted_86_557]
                     [bha=bha_563 & bha=bha_562 & bha=bha_561 & 1<=bha_563]
                     [0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(flted_87_555,flted_87_556,
                                bha1: res::rb<flted_87_556,flted_87_555,bha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_87_556 & flted_87_556=3+na+nb+nc+
                                   nd]
                                 [0=flted_87_555][1<=bha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                  bha](ex)a::rb<na,flted_86_560,bha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_86_559,bha_561>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_86_558,bha_562>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  d::rb<nd,flted_86_557,bha_563>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([bha_562=bha & bha_562=bha_563 & bha_562=bha_561 & 
                     1<=bha_562]
                   [0<=na][0<=nb][0<=nc][0<=nd][0=flted_86_560]
                   [0=flted_86_559][0=flted_86_558][0=flted_86_557]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(flted_87_4368,flted_87_4369,
                              bha1_4370: res::rb<flted_87_4368,flted_87_4369,bha1_4370>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([flted_87_4368=3+na+nb+nc+nd & 0<=na & 
                                 0<=nc & 0<=nd & 0<=nb]
                               [res!=null][-1+bha1_4370=bha & 1<=bha]
                               [0=flted_87_4369][1<=bha_563]
                               [0<=flted_86_557 & flted_86_557<=1]
                               [1<=bha_562]
                               [0<=flted_86_558 & flted_86_558<=1]
                               [1<=bha_561]
                               [0<=flted_86_559 & flted_86_559<=1]
                               [0<=flted_86_560 & flted_86_560<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure del$node~int... 
!!! REL :  DEL1(bh,bh1)
!!! POST:  1=bh1 & 1=bh
!!! PRE :  true
!!! REL :  DEL2(bh,bh2)
!!! POST:  bh2>=1 & 2>=bh2 & 2=bh
!!! PRE :  true
!!! REL :  DEL3(bh,bh3)
!!! POST:  1=bh3 & 1=bh
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL1,DEL2,DEL3]
              EBase exists (Expl)(Impl)[n; cl; 
                    bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=cl & cl<=1][0<=n][1<=bh]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::ref [x]
                                
                                EXISTS(flted_463_116,bh1,
                                cl2: x'::rb<flted_463_116,cl2,bh1>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                (
                                ([0<=flted_463_116 & 1+flted_463_116=n]
                                 [1<=bh1 & DEL1(bh,bh1)][1=cl]
                                 [0<=cl2 & cl2<=1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_464_117,flted_464_118,
                                   bh2: x'::rb<flted_464_118,flted_464_117,bh2>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                   (
                                   ([0<=flted_464_118 & 1+flted_464_118=n]
                                    [0=flted_464_117][1<=bh2 & DEL2(bh,bh2)]
                                    [0=cl]))&
                                   {FLOW,(20,21)=__norm})
                                or EXISTS(n_119,cl_120,
                                   bh3: x'::rb<n_119,cl_120,bh3>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                   (
                                   ([1<=bh3 & DEL3(bh,bh3)]
                                    [n=n_119 & 0<=n_119]
                                    [cl=cl_120 & cl_120<=1 & 0<=cl_120]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; cl; 
                  bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][1<=bh][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::ref [x]
                              
                              EXISTS(flted_464_6951,flted_464_6952,
                              bh2_6953: x'::rb<flted_464_6952,flted_464_6951,bh2_6953>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([bh=2 & 1<=bh][bh2_6953<=2 & 1<=bh2_6953]
                               [cl=0 & 0<=cl & cl<=1][0=flted_464_6951]
                               [0<=flted_464_6952 & 0<=n & 1+flted_464_6952=n]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_463_6954,bh1_6955,
                                 cl2_6956: x'::rb<flted_463_6954,cl2_6956,bh1_6955>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                 (
                                 ([bh=1 & 1<=bh][1=bh1_6955 & 1<=bh1_6955]
                                  [0<=cl2_6956 & cl2_6956<=1]
                                  [cl=1 & 0<=cl & cl<=1]
                                  [0<=flted_463_6954 & 0<=n & 1+
                                    flted_463_6954=n]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(n_6957,cl_6958,
                                 bh3_6959: x'::rb<n_6957,cl_6958,bh3_6959>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                 (
                                 ([bh=1 & 1<=bh][1=bh3_6959 & 1<=bh3_6959]
                                  [cl=cl_6958 & cl<=1 & 0<=cl]
                                  [n=n_6957 & 0<=n]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (bh1=1 & bh=1) --> DEL1(bh,bh1),
 (bh2=2 & bh=2) --> DEL2(bh,bh2),
 (bh=1 & bh1=1) --> DEL1(bh,bh1),
 (bh2=1 & bh=2) --> DEL2(bh,bh2),
 (bh3=1 & bh=1) --> DEL3(bh,bh3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$node~int SUCCESS

Checking procedure del_2$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; h; nb; 
                    nc](ex)EXISTS(flted_309_178,flted_309_179,flted_309_180,
                    flted_309_181,
                    flted_309_182: a::rb<na,flted_309_182,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_309_181,flted_309_180>@M[Orig][LHSCase]@ rem br[{696}] * 
                    c::rb<nc,flted_309_179,flted_309_178>@M[Orig][LHSCase]@ rem br[{696}]&
                    (
                    ([0=flted_309_182][flted_309_181=0][flted_309_179=0]
                     [1<=h & -1+flted_309_178=h & -1+flted_309_180=h]
                     [null!=b][null!=c][0<=na][0<=nb & 0!=nb][0<=nc & 0!=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(flted_310_176,flted_310_177,
                                h1: res::rb<flted_310_177,flted_310_176,h1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_310_177 & flted_310_177=2+na+nb+nc]
                                 [0=flted_310_176][1<=h1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; h; nb; 
                  nc](ex)a::rb<na,flted_309_182,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_309_181,flted_309_180>@M[Orig][LHSCase]@ rem br[{696}] * 
                  c::rb<nc,flted_309_179,flted_309_178>@M[Orig][LHSCase]@ rem br[{696}]&
                  (
                  ([flted_309_178=flted_309_180 & 1+h=flted_309_178 & 
                     2<=flted_309_178]
                   [b!=null][c!=null][0<=na][1<=nb][1<=nc][0=flted_309_182]
                   [0=flted_309_181][0=flted_309_179]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              
                              EXISTS(v_7566,flted_13_7567,l_7568,r_7569,
                              flted_310_7570,flted_310_7571,
                              h1_7572: b::node<v_7566,flted_13_7567,l_7568,r_7569>@M[Orig][] * 
                              res::rb<flted_310_7570,flted_310_7571,h1_7572>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([b!=null]
                               [2+na+nb+nc=flted_310_7570 & (3+na+
                                 nb)<=flted_310_7570 & 0<=nb & 0<=na & 
                                 0<=nc & 1<=nb]
                               [res!=null][-2+h1_7572=h & 1<=h][c!=null]
                               [0=flted_13_7567][0=flted_310_7571]
                               [1<=flted_309_178]
                               [0<=flted_309_179 & flted_309_179<=1]
                               [1<=flted_309_180]
                               [0<=flted_309_181 & flted_309_181<=1]
                               [0<=flted_309_182 & flted_309_182<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_7573,flted_13_7574,r_7575,l_7576,
                                 v_7577,flted_12_7578,l_7579,r_7580,
                                 flted_310_7581,flted_310_7582,
                                 h1_7583: b::node<v_7573,flted_13_7574,l_7576,r_7575>@M[Orig][] * 
                                 l_7576::node<v_7577,flted_12_7578,l_7579,r_7580>@M[Orig][] * 
                                 res::rb<flted_310_7581,flted_310_7582,h1_7583>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                 (
                                 ([c!=null][b!=null][-2+h1_7583=h & 1<=h]
                                  [flted_310_7581=2+na+nb+nc & 2<=nb & 
                                    0<=nb & 1<=nc & 0<=nc & 0<=na]
                                  [l_7576!=null][res!=null][1=flted_12_7578]
                                  [0=flted_13_7574][0=flted_310_7582]
                                  [1<=flted_309_178]
                                  [0<=flted_309_179 & flted_309_179<=1]
                                  [1<=flted_309_180]
                                  [0<=flted_309_181 & flted_309_181<=1]
                                  [0<=flted_309_182 & flted_309_182<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_7584,flted_13_7585,l_7586,r_7587,
                                 flted_310_7588,flted_310_7589,
                                 h1_7590: b::node<v_7584,flted_13_7585,l_7586,r_7587>@M[Orig][] * 
                                 res::rb<flted_310_7588,flted_310_7589,h1_7590>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                 (
                                 ([2+na+nb+nc=flted_310_7588 & (3+na+
                                    nb)<=flted_310_7588 & 0<=nb & 2<=nb & 
                                    0<=nc & 0<=na]
                                  [r_7587!=null][res!=null][c!=null][
                                  b!=null][-2+h1_7590=h & 1<=h]
                                  [0=flted_13_7585][0=flted_310_7589]
                                  [1<=flted_309_178]
                                  [0<=flted_309_179 & flted_309_179<=1]
                                  [1<=flted_309_180]
                                  [0<=flted_309_181 & flted_309_181<=1]
                                  [0<=flted_309_182 & flted_309_182<=1]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_2$node~node~node SUCCESS

Checking procedure del_2r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    h](ex)EXISTS(flted_336_146,flted_336_147,flted_336_148,
                    flted_336_149,
                    flted_336_150: a::rb<na,flted_336_150,flted_336_149>@M[Orig][LHSCase]@ rem br[{696}] * 
                    b::rb<nb,flted_336_148,flted_336_147>@M[Orig][LHSCase]@ rem br[{696}] * 
                    c::rb<nc,flted_336_146,h>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_336_150][flted_336_148=0]
                     [1<=flted_336_149 & 1!=flted_336_147 & -1+
                       flted_336_147=h & -1+flted_336_149=h]
                     [0=flted_336_146][null!=b][0!=na & 0<=na][0<=nb & 0!=nb]
                     [0<=nc][null!=a]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 56::
                                EXISTS(flted_337_144,flted_337_145,
                                h1: res::rb<flted_337_145,flted_337_144,h1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_337_145 & flted_337_145=2+na+nb+nc]
                                 [0=flted_337_144][1<=h1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  h](ex)a::rb<na,flted_336_150,flted_336_149>@M[Orig][LHSCase]@ rem br[{696}] * 
                  b::rb<nb,flted_336_148,flted_336_147>@M[Orig][LHSCase]@ rem br[{696}] * 
                  c::rb<nc,flted_336_146,h>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([flted_336_147=flted_336_149 & 1+h=flted_336_147 & 
                     2<=flted_336_147]
                   [b!=null][1<=na][1<=nb][0<=nc][a!=null][0=flted_336_150]
                   [0=flted_336_148][0=flted_336_146]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 56::
                              
                              EXISTS(v_8214,flted_13_8215,l_8216,r_8217,
                              flted_337_8218,flted_337_8219,
                              h1_8220: b::node<v_8214,flted_13_8215,l_8216,r_8217>@M[Orig][] * 
                              res::rb<flted_337_8218,flted_337_8219,h1_8220>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=flted_337_8218 & 0<=na & (3+nb+
                                 nc)<=flted_337_8218 & 0<=nb & 0<=nc & 1<=nb]
                               [b!=null][a!=null][-2+h1_8220=h & 1<=h]
                               [res!=null][0=flted_13_8215][0=flted_337_8219]
                               [0<=flted_336_146 & flted_336_146<=1]
                               [1<=flted_336_147]
                               [0<=flted_336_148 & flted_336_148<=1]
                               [1<=flted_336_149]
                               [0<=flted_336_150 & flted_336_150<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_8221,flted_13_8222,l_8223,r_8224,
                                 v_8225,flted_12_8226,l_8227,r_8228,
                                 flted_337_8229,flted_337_8230,
                                 h1_8231: b::node<v_8221,flted_13_8222,l_8223,r_8224>@M[Orig][] * 
                                 r_8224::node<v_8225,flted_12_8226,l_8227,r_8228>@M[Orig][] * 
                                 res::rb<flted_337_8229,flted_337_8230,h1_8231>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                 (
                                 ([2+na+nb+nc=flted_337_8229 & 0<=na & (3+nb+
                                    nc)<=flted_337_8229 & 0<=nb & 2<=nb & 
                                    0<=nc]
                                  [r_8224!=null][b!=null]
                                  [-2+h1_8231=h & 1<=h][a!=null][res!=null]
                                  [0=flted_13_8222][1=flted_12_8226]
                                  [0=flted_337_8230]
                                  [0<=flted_336_146 & flted_336_146<=1]
                                  [1<=flted_336_147]
                                  [0<=flted_336_148 & flted_336_148<=1]
                                  [1<=flted_336_149]
                                  [0<=flted_336_150 & flted_336_150<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_8232,flted_13_8233,l_8234,r_8235,
                                 flted_337_8236,flted_337_8237,
                                 h1_8238: b::node<v_8232,flted_13_8233,l_8234,r_8235>@M[Orig][] * 
                                 res::rb<flted_337_8236,flted_337_8237,h1_8238>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                 (
                                 ([-2+h1_8238=h & 1<=h]
                                  [2+na+nb+nc=flted_337_8236 & 0<=na & (2+na+
                                    nb)<=flted_337_8236 & 0<=nb & 2<=nb & 
                                    0<=nc & 1<=na]
                                  [a!=null][b!=null][l_8234!=null][res!=null]
                                  [0=flted_13_8233][0=flted_337_8237]
                                  [0<=flted_336_146 & flted_336_146<=1]
                                  [1<=flted_336_147]
                                  [0<=flted_336_148 & flted_336_148<=1]
                                  [1<=flted_336_149]
                                  [0<=flted_336_150 & flted_336_150<=1]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_2r$node~node~node SUCCESS

Checking procedure del_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; ha](ex)EXISTS(ha_237,
                    ha_238,flted_275_234,flted_275_235,
                    flted_275_236: a::rb<na,flted_275_236,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_275_235,ha_237>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_275_234,ha_238>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_275_236][0=flted_275_235][0=flted_275_234]
                     [ha=ha_238 & ha=ha_237 & 1<=ha_238][0<=na][0<=nb][
                     0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(flted_276_232,flted_276_233,
                                ha1: res::rb<flted_276_233,flted_276_232,ha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_276_233 & flted_276_233=2+na+nb+nc]
                                 [0=flted_276_232][1<=ha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  ha](ex)a::rb<na,flted_275_236,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_275_235,ha_237>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_275_234,ha_238>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([ha_237=ha & ha_237=ha_238 & 1<=ha_237][0<=na][0<=nb]
                   [0<=nc][0=flted_275_236][0=flted_275_235][0=flted_275_234]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(flted_276_8367,flted_276_8368,
                              ha1_8369: res::rb<flted_276_8367,flted_276_8368,ha1_8369>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=flted_276_8367 & 0<=na & (2+nb+
                                 nc)<=flted_276_8367 & 0<=nc & 0<=nb]
                               [1+ha=ha1_8369 & 1<=ha & 2<=ha1_8369]
                               [res!=null][0=flted_276_8368][1<=ha_238]
                               [0<=flted_275_234 & flted_275_234<=1]
                               [1<=ha_237]
                               [0<=flted_275_235 & flted_275_235<=1]
                               [0<=flted_275_236 & flted_275_236<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; ha](ex)EXISTS(ha_210,
                    ha_211,flted_292_207,flted_292_208,
                    flted_292_209: a::rb<na,flted_292_209,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_292_208,ha_210>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_292_207,ha_211>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_292_209][0=flted_292_208][0=flted_292_207]
                     [ha=ha_211 & ha=ha_210 & 1<=ha_211][0<=na][0<=nb][
                     0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(flted_293_205,flted_293_206,
                                ha1: res::rb<flted_293_206,flted_293_205,ha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_293_206 & flted_293_206=2+na+nb+nc]
                                 [0=flted_293_205][1<=ha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  ha](ex)a::rb<na,flted_292_209,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_292_208,ha_210>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_292_207,ha_211>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([ha_210=ha & ha_210=ha_211 & 1<=ha_210][0<=na][0<=nb]
                   [0<=nc][0=flted_292_209][0=flted_292_208][0=flted_292_207]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(flted_293_8498,flted_293_8499,
                              ha1_8500: res::rb<flted_293_8498,flted_293_8499,ha1_8500>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=flted_293_8498 & (2+na+
                                 nc)<=flted_293_8498 & 0<=nb & 0<=na & 0<=nc]
                               [1+ha=ha1_8500 & 1<=ha & 2<=ha1_8500]
                               [res!=null][0=flted_293_8499][1<=ha_211]
                               [0<=flted_292_207 & flted_292_207<=1]
                               [1<=ha_210]
                               [0<=flted_292_208 & flted_292_208<=1]
                               [0<=flted_292_209 & flted_292_209<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; ha](ex)EXISTS(ha_291,
                    ha_292,flted_242_288,flted_242_289,
                    flted_242_290: a::rb<na,flted_242_290,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_242_289,ha_291>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_242_288,ha_292>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_242_290][0=flted_242_289][0=flted_242_288]
                     [ha=ha_292 & ha=ha_291 & 1<=ha_292][0<=na][0<=nb][
                     0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_243_286,flted_243_287,
                                ha1: res::rb<flted_243_287,flted_243_286,ha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_243_287 & flted_243_287=2+na+nb+nc]
                                 [0=flted_243_286][1<=ha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  ha](ex)a::rb<na,flted_242_290,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_242_289,ha_291>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_242_288,ha_292>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([ha_291=ha & ha_291=ha_292 & 1<=ha_291][0<=na][0<=nb]
                   [0<=nc][0=flted_242_290][0=flted_242_289][0=flted_242_288]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_243_8637,flted_243_8638,
                              ha1_8639: res::rb<flted_243_8637,flted_243_8638,ha1_8639>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([flted_243_8637=2+na+nb+nc & 0<=na & 0<=nb & 
                                 0<=nc]
                               [1+ha=ha1_8639 & 1<=ha & 2<=ha1_8639]
                               [res!=null][0=flted_243_8638][1<=ha_292]
                               [0<=flted_242_288 & flted_242_288<=1]
                               [1<=ha_291]
                               [0<=flted_242_289 & flted_242_289<=1]
                               [0<=flted_242_290 & flted_242_290<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; ha](ex)EXISTS(ha_264,
                    ha_265,flted_258_261,flted_258_262,
                    flted_258_263: a::rb<na,flted_258_263,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_258_262,ha_264>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_258_261,ha_265>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_258_263][0=flted_258_262][0=flted_258_261]
                     [ha=ha_265 & ha=ha_264 & 1<=ha_265][0<=na][0<=nb][
                     0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                EXISTS(flted_259_259,flted_259_260,
                                ha1: res::rb<flted_259_260,flted_259_259,ha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_259_260 & flted_259_260=2+na+nb+nc]
                                 [0=flted_259_259][1<=ha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  ha](ex)a::rb<na,flted_258_263,ha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_258_262,ha_264>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_258_261,ha_265>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([ha_264=ha & ha_264=ha_265 & 1<=ha_264][0<=na][0<=nb]
                   [0<=nc][0=flted_258_263][0=flted_258_262][0=flted_258_261]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              EXISTS(flted_259_8768,flted_259_8769,
                              ha1_8770: res::rb<flted_259_8768,flted_259_8769,ha1_8770>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=flted_259_8768 & (2+na+
                                 nc)<=flted_259_8768 & 0<=nb & 0<=na & 0<=nc]
                               [1+ha=ha1_8770 & 1<=ha & 2<=ha1_8770]
                               [res!=null][0=flted_259_8769][1<=ha_265]
                               [0<=flted_258_261 & flted_258_261<=1]
                               [1<=ha_264]
                               [0<=flted_258_262 & flted_258_262<=1]
                               [0<=flted_258_263 & flted_258_263<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                    h](ex)
                          EXISTS(h_398,h_399,h_400,flted_203_390,
                          flted_203_391,flted_203_392,
                          flted_203_393: a::rb<na,flted_203_393,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          b::rb<nb,flted_203_392,h_398>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          c::rb<nc,flted_203_391,h_399>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          d::rb<nd,flted_203_390,h_400>@M[Orig][LHSCase]@ rem br[{698,696}]&
                          (
                          ([0=flted_203_393][0=flted_203_392]
                           [0=flted_203_391][0=flted_203_390][0=color]
                           [h=h_400 & h=h_399 & h=h_398 & 1<=h_400][0<=na]
                           [0<=nb][0<=nc][0<=nd]))&
                          {FLOW,(20,21)=__norm})
                          or EXISTS(h_401,h_402,h_403,flted_204_394,
                             flted_204_395,flted_204_396,
                             flted_204_397: a::rb<na,flted_204_397,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             b::rb<nb,flted_204_396,h_401>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             c::rb<nc,flted_204_395,h_402>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             d::rb<nd,flted_204_394,h_403>@M[Orig][LHSCase]@ rem br[{698,696}]&
                             (
                             ([0=flted_204_397][0=flted_204_396]
                              [0=flted_204_395][0=flted_204_394][1=color]
                              [h=h_403 & h=h_402 & h=h_401 & 1<=h_403][
                              0<=na][0<=nb][0<=nc][0<=nd]))&
                             {FLOW,(20,21)=__norm})
                          
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 32::
                                
                                EXISTS(flted_205_386,flted_205_387,
                                h1: res::rb<flted_205_387,flted_205_386,h1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_205_387 & flted_205_387=3+na+nb+
                                   nc+nd]
                                 [0=flted_205_386][0=color][1<=h1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_206_388,flted_206_389,
                                   h2: res::rb<flted_206_389,flted_206_388,h2>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([0!=flted_206_389 & 0<=flted_206_389 & 
                                      flted_206_389=3+na+nb+nc+nd]
                                    [flted_206_388=1][1=color][1<=h2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                  h](ex)
                        a::rb<na,flted_203_393,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        b::rb<nb,flted_203_392,h_398>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        c::rb<nc,flted_203_391,h_399>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        d::rb<nd,flted_203_390,h_400>@M[Orig][LHSCase]@ rem br[{698,696}]&
                        (
                        ([h_399=h & h_399=h_400 & h_399=h_398 & 1<=h_399]
                         [0<=na][0<=nb][0<=nc][0<=nd][0=flted_203_393]
                         [0=flted_203_392][0=flted_203_391][0=flted_203_390]
                         [0=color]))&
                        {FLOW,(20,21)=__norm}
                        or a::rb<na,flted_204_397,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           b::rb<nb,flted_204_396,h_401>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           c::rb<nc,flted_204_395,h_402>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           d::rb<nd,flted_204_394,h_403>@M[Orig][LHSCase]@ rem br[{698,696}]&
                           (
                           ([h_402=h & h_402=h_403 & h_402=h_401 & 1<=h_402]
                            [0<=na][0<=nb][0<=nc][0<=nd][0=flted_204_397]
                            [0=flted_204_396][0=flted_204_395]
                            [0=flted_204_394][1=color]))&
                           {FLOW,(20,21)=__norm}
                        
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 32::
                              
                              EXISTS(flted_205_9139,flted_205_9140,
                              h1_9141: res::rb<flted_205_9139,flted_205_9140,h1_9141>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([(0<=flted_203_393 & flted_203_393<=1 & 
                                 1<=h & 0<=na & 0<=flted_203_392 & 
                                 flted_203_392<=1 & 1<=h_398 & 0<=nb & 
                                 0<=flted_203_391 & flted_203_391<=1 & 
                                 1<=h_399 & 0<=nc & 0<=flted_203_390 & 
                                 flted_203_390<=1 & 1<=h_400 & 0<=nd | 
                                 0<=flted_204_397 & flted_204_397<=1 & 
                                 1<=h & 0<=na & 0<=flted_204_396 & 
                                 flted_204_396<=1 & 1<=h_401 & 0<=nb & 
                                 0<=flted_204_395 & flted_204_395<=1 & 
                                 1<=h_402 & 0<=nc & 0<=flted_204_394 & 
                                 flted_204_394<=1 & 1<=h_403 & 0<=nd) & 
                                 flted_205_9139=3+na+nb+nc+nd & 1<=h & 
                                 0<=nd & -2+h1_9141=h & 0<=nc & 0<=nb & 0<=na]
                               [res!=null][0=flted_205_9140][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_206_9142,flted_206_9143,
                                 h2_9144: res::rb<flted_206_9142,flted_206_9143,h2_9144>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([(0<=flted_203_393 & flted_203_393<=1 & 
                                    1<=h & 0<=na & 0<=flted_203_392 & 
                                    flted_203_392<=1 & 1<=h_398 & 0<=nb & 
                                    0<=flted_203_391 & flted_203_391<=1 & 
                                    1<=h_399 & 0<=nc & 0<=flted_203_390 & 
                                    flted_203_390<=1 & 1<=h_400 & 0<=nd | 
                                    0<=flted_204_397 & flted_204_397<=1 & 
                                    1<=h & 0<=na & 0<=flted_204_396 & 
                                    flted_204_396<=1 & 1<=h_401 & 0<=nb & 
                                    0<=flted_204_395 & flted_204_395<=1 & 
                                    1<=h_402 & 0<=nc & 0<=flted_204_394 & 
                                    flted_204_394<=1 & 1<=h_403 & 0<=nd) & 3+
                                    na+nb+nc+nd=flted_206_9142 & 1<=h & (3+
                                    nb+nc+nd)<=flted_206_9142 & -1+
                                    h2_9144=h & 0<=nc & 0<=nb & 0<=nd]
                                  [res!=null][1=flted_206_9143][1=color]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5$node~node~node~node~int SUCCESS

Checking procedure del_5r$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                    h](ex)
                          EXISTS(h_333,h_334,h_335,flted_224_325,
                          flted_224_326,flted_224_327,
                          flted_224_328: a::rb<na,flted_224_328,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          b::rb<nb,flted_224_327,h_333>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          c::rb<nc,flted_224_326,h_334>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          d::rb<nd,flted_224_325,h_335>@M[Orig][LHSCase]@ rem br[{698,696}]&
                          (
                          ([0=flted_224_328][0=flted_224_327]
                           [0=flted_224_326][0=flted_224_325][0=color]
                           [h=h_335 & h=h_334 & h=h_333 & 1<=h_335][0<=na]
                           [0<=nb][0<=nc][0<=nd]))&
                          {FLOW,(20,21)=__norm})
                          or EXISTS(h_336,h_337,h_338,flted_225_329,
                             flted_225_330,flted_225_331,
                             flted_225_332: a::rb<na,flted_225_332,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             b::rb<nb,flted_225_331,h_336>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             c::rb<nc,flted_225_330,h_337>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             d::rb<nd,flted_225_329,h_338>@M[Orig][LHSCase]@ rem br[{698,696}]&
                             (
                             ([0=flted_225_332][0=flted_225_331]
                              [0=flted_225_330][0=flted_225_329][1=color]
                              [h=h_338 & h=h_337 & h=h_336 & 1<=h_338][
                              0<=na][0<=nb][0<=nc][0<=nd]))&
                             {FLOW,(20,21)=__norm})
                          
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                
                                EXISTS(flted_226_321,flted_226_322,
                                h1: res::rb<flted_226_322,flted_226_321,h1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_226_322 & flted_226_322=3+na+nb+
                                   nc+nd]
                                 [0=flted_226_321][0=color][1<=h1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_227_323,flted_227_324,
                                   h2: res::rb<flted_227_324,flted_227_323,h2>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([0!=flted_227_324 & 0<=flted_227_324 & 
                                      flted_227_324=3+na+nb+nc+nd]
                                    [flted_227_323=1][1=color][1<=h2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; nd; 
                  h](ex)
                        a::rb<na,flted_224_328,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        b::rb<nb,flted_224_327,h_333>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        c::rb<nc,flted_224_326,h_334>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        d::rb<nd,flted_224_325,h_335>@M[Orig][LHSCase]@ rem br[{698,696}]&
                        (
                        ([h_334=h & h_334=h_335 & h_334=h_333 & 1<=h_334]
                         [0<=na][0<=nb][0<=nc][0<=nd][0=flted_224_328]
                         [0=flted_224_327][0=flted_224_326][0=flted_224_325]
                         [0=color]))&
                        {FLOW,(20,21)=__norm}
                        or a::rb<na,flted_225_332,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           b::rb<nb,flted_225_331,h_336>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           c::rb<nc,flted_225_330,h_337>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           d::rb<nd,flted_225_329,h_338>@M[Orig][LHSCase]@ rem br[{698,696}]&
                           (
                           ([h_337=h & h_337=h_338 & h_337=h_336 & 1<=h_337]
                            [0<=na][0<=nb][0<=nc][0<=nd][0=flted_225_332]
                            [0=flted_225_331][0=flted_225_330]
                            [0=flted_225_329][1=color]))&
                           {FLOW,(20,21)=__norm}
                        
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              
                              EXISTS(flted_226_9548,flted_226_9549,
                              h1_9550: res::rb<flted_226_9548,flted_226_9549,h1_9550>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([(0<=flted_224_328 & flted_224_328<=1 & 
                                 1<=h & 0<=na & 0<=flted_224_327 & 
                                 flted_224_327<=1 & 1<=h_333 & 0<=nb & 
                                 0<=flted_224_326 & flted_224_326<=1 & 
                                 1<=h_334 & 0<=nc & 0<=flted_224_325 & 
                                 flted_224_325<=1 & 1<=h_335 & 0<=nd | 
                                 0<=flted_225_332 & flted_225_332<=1 & 
                                 1<=h & 0<=na & 0<=flted_225_331 & 
                                 flted_225_331<=1 & 1<=h_336 & 0<=nb & 
                                 0<=flted_225_330 & flted_225_330<=1 & 
                                 1<=h_337 & 0<=nc & 0<=flted_225_329 & 
                                 flted_225_329<=1 & 1<=h_338 & 0<=nd) & 
                                 flted_226_9548=3+na+nb+nc+nd & 1<=h & 
                                 0<=na & -2+h1_9550=h & 0<=nc & 0<=nb & 0<=nd]
                               [res!=null][0=flted_226_9549][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_227_9551,flted_227_9552,
                                 h2_9553: res::rb<flted_227_9551,flted_227_9552,h2_9553>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([(0<=flted_224_328 & flted_224_328<=1 & 
                                    1<=h & 0<=na & 0<=flted_224_327 & 
                                    flted_224_327<=1 & 1<=h_333 & 0<=nb & 
                                    0<=flted_224_326 & flted_224_326<=1 & 
                                    1<=h_334 & 0<=nc & 0<=flted_224_325 & 
                                    flted_224_325<=1 & 1<=h_335 & 0<=nd | 
                                    0<=flted_225_332 & flted_225_332<=1 & 
                                    1<=h & 0<=na & 0<=flted_225_331 & 
                                    flted_225_331<=1 & 1<=h_336 & 0<=nb & 
                                    0<=flted_225_330 & flted_225_330<=1 & 
                                    1<=h_337 & 0<=nc & 0<=flted_225_329 & 
                                    flted_225_329<=1 & 1<=h_338 & 0<=nd) & 3+
                                    na+nb+nc+nd=flted_227_9551 & 1<=h & (3+
                                    nb+nc+nd)<=flted_227_9551 & -1+
                                    h2_9553=h & 0<=nc & 0<=nb & 0<=nd]
                                  [res!=null][1=flted_227_9552][1=color]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5r$node~node~node~node~int SUCCESS

Checking procedure del_6$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; nc; 
                    h](ex)
                          EXISTS(h_500,h_501,flted_159_496,
                          flted_159_497: a::rb<na,flted_159_497,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                          b::rb<nb,Anon_15,h_500>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                          c::rb<nc,flted_159_496,h_501>@M[Orig][LHSCase]@ rem br[{697}]&
                          (
                          ([0=flted_159_497][flted_159_496=1][0=color]
                           [h=h_501 & h=h_500 & 1<=h_501][0<=na][0<=nb]
                           [Anon_15<=1 & 0<=Anon_15][0<=nc & 0!=nc][null!=c]))&
                          {FLOW,(20,21)=__norm})
                          or EXISTS(h_502,h_503,flted_160_498,
                             flted_160_499: a::rb<na,flted_160_499,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                             b::rb<nb,Anon_16,h_502>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                             c::rb<nc,flted_160_498,h_503>@M[Orig][LHSCase]@ rem br[{697}]&
                             (
                             ([0=flted_160_499][flted_160_498=1][1=color]
                              [h=h_503 & h=h_502 & 1<=h_503][0<=na][0<=nb]
                              [Anon_16<=1 & 0<=Anon_16][0<=nc & 0!=nc]
                              [null!=c]))&
                             {FLOW,(20,21)=__norm})
                          
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 24::
                                
                                EXISTS(flted_161_492,flted_161_493,
                                h1: res::rb<flted_161_493,flted_161_492,h1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_161_493 & flted_161_493=2+na+nb+nc]
                                 [0=flted_161_492][0=color][1<=h1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_162_494,flted_162_495,
                                   h2: res::rb<flted_162_495,flted_162_494,h2>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([0!=flted_162_495 & 0<=flted_162_495 & 
                                      flted_162_495=2+na+nb+nc]
                                    [flted_162_494=1][1=color][1<=h2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; nc; 
                  h](ex)
                        a::rb<na,flted_159_497,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                        b::rb<nb,Anon_15,h_500>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                        c::rb<nc,flted_159_496,h_501>@M[Orig][LHSCase]@ rem br[{697}]&
                        (
                        ([h_500=h & h_500=h_501 & 1<=h_500][0<=na][0<=nb]
                         [1<=nc][c!=null][0=flted_159_497][1=flted_159_496]
                         [0=color][Anon_15<=1 & 0<=Anon_15]))&
                        {FLOW,(20,21)=__norm}
                        or a::rb<na,flted_160_499,h>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           b::rb<nb,Anon_16,h_502>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                           c::rb<nc,flted_160_498,h_503>@M[Orig][LHSCase]@ rem br[{697}]&
                           (
                           ([h_502=h & h_502=h_503 & 1<=h_502][0<=na][
                            0<=nb][1<=nc][c!=null][0=flted_160_499]
                            [1=flted_160_498][1=color]
                            [Anon_16<=1 & 0<=Anon_16]))&
                           {FLOW,(20,21)=__norm}
                        
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 24::
                              
                              EXISTS(flted_161_10154,flted_161_10155,
                              h1_10156: res::rb<flted_161_10154,flted_161_10155,h1_10156>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_159_497 & flted_159_497<=1 & 
                                 1<=h & 0<=na & 0<=Anon_15 & Anon_15<=1 & 
                                 1<=h_500 & 0<=nb & 0<=flted_159_496 & 
                                 flted_159_496<=1 & 1<=h_501 & 0<=nc | 
                                 0<=flted_160_499 & flted_160_499<=1 & 
                                 1<=h & 0<=na & 0<=Anon_16 & Anon_16<=1 & 
                                 1<=h_502 & 0<=nb & 0<=flted_160_498 & 
                                 flted_160_498<=1 & 1<=h_503 & 0<=nc) & 2+na+
                                 nb+nc=flted_161_10154 & 3<=h1_10156 & (2+nb+
                                 nc)<=flted_161_10154 & 2+h=h1_10156 & 
                                 0<=nb & 1<=nc]
                               [res!=null][c!=null][0=color]
                               [0=flted_161_10155]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_162_10157,flted_162_10158,
                                 h2_10159: res::rb<flted_162_10157,flted_162_10158,h2_10159>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([Anon_16<=1 & 0<=Anon_16 & 
                                    (0<=flted_159_497 & flted_159_497<=1 & 
                                    1<=h & 0<=na & 0<=Anon_15 & Anon_15<=1 & 
                                    1<=h_500 & 0<=nb & 0<=flted_159_496 & 
                                    flted_159_496<=1 & 1<=h_501 & 0<=nc | 
                                    0<=flted_160_499 & flted_160_499<=1 & 
                                    1<=h & 0<=na & 0<=Anon_16 & Anon_16<=1 & 
                                    1<=h_502 & 0<=nb & 0<=flted_160_498 & 
                                    flted_160_498<=1 & 1<=h_503 & 0<=nc) & 2+
                                    na+nb+nc=flted_162_10157 & 2<=h2_10159 & 
                                    (2+nb+nc)<=flted_162_10157 & 1+
                                    h=h2_10159 & 0<=nb & 1<=nc]
                                  [res!=null][c!=null][1=color]
                                  [1=flted_162_10158]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6$node~node~node~int SUCCESS

Checking procedure del_6r$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; nc; 
                    ha](ex)
                           EXISTS(ha_455,ha_456,flted_181_451,
                           flted_181_452: a::rb<na,flted_181_452,ha>@M[Orig][LHSCase]@ rem br[{697}] * 
                           b::rb<nb,Anon_19,ha_455>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                           c::rb<nc,flted_181_451,ha_456>@M[Orig][LHSCase]@ rem br[{698,696}]&
                           (
                           ([flted_181_452=1][0=flted_181_451][0=color]
                            [ha=ha_456 & ha=ha_455 & 1<=ha_456]
                            [0<=na & 0!=na][null!=a][0<=nb]
                            [Anon_19<=1 & 0<=Anon_19][0<=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(ha_457,ha_458,flted_182_453,
                              flted_182_454: a::rb<na,flted_182_454,ha>@M[Orig][LHSCase]@ rem br[{697}] * 
                              b::rb<nb,Anon_20,ha_457>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                              c::rb<nc,flted_182_453,ha_458>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([flted_182_454=1][0=flted_182_453][1=color]
                               [ha=ha_458 & ha=ha_457 & 1<=ha_458]
                               [0<=na & 0!=na][null!=a][0<=nb]
                               [Anon_20<=1 & 0<=Anon_20][0<=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                
                                EXISTS(flted_183_447,flted_183_448,
                                ha1: res::rb<flted_183_448,flted_183_447,ha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_183_448 & flted_183_448=2+na+nb+nc]
                                 [0=flted_183_447][0=color][1<=ha1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_184_449,flted_184_450,
                                   ha2: res::rb<flted_184_450,flted_184_449,ha2>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([0!=flted_184_450 & 0<=flted_184_450 & 
                                      flted_184_450=2+na+nb+nc]
                                    [flted_184_449=1][1=color][1<=ha2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; nc; 
                  ha](ex)
                         a::rb<na,flted_181_452,ha>@M[Orig][LHSCase]@ rem br[{697}] * 
                         b::rb<nb,Anon_19,ha_455>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                         c::rb<nc,flted_181_451,ha_456>@M[Orig][LHSCase]@ rem br[{698,696}]&
                         (
                         ([ha_455=ha & ha_455=ha_456 & 1<=ha_455][1<=na]
                          [a!=null][0<=nb][0<=nc][1=flted_181_452]
                          [0=flted_181_451][0=color][Anon_19<=1 & 0<=Anon_19]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb<na,flted_182_454,ha>@M[Orig][LHSCase]@ rem br[{697}] * 
                            b::rb<nb,Anon_20,ha_457>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                            c::rb<nc,flted_182_453,ha_458>@M[Orig][LHSCase]@ rem br[{698,696}]&
                            (
                            ([ha_457=ha & ha_457=ha_458 & 1<=ha_457][
                             1<=na][a!=null][0<=nb][0<=nc][1=flted_182_454]
                             [0=flted_182_453][1=color]
                             [Anon_20<=1 & 0<=Anon_20]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              
                              EXISTS(flted_183_10780,flted_183_10781,
                              ha1_10782: res::rb<flted_183_10780,flted_183_10781,ha1_10782>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_181_452 & flted_181_452<=1 & 
                                 1<=ha & 0<=na & 0<=Anon_19 & Anon_19<=1 & 
                                 1<=ha_455 & 0<=nb & 0<=flted_181_451 & 
                                 flted_181_451<=1 & 1<=ha_456 & 0<=nc | 
                                 0<=flted_182_454 & flted_182_454<=1 & 
                                 1<=ha & 0<=na & 0<=Anon_20 & Anon_20<=1 & 
                                 1<=ha_457 & 0<=nb & 0<=flted_182_453 & 
                                 flted_182_453<=1 & 1<=ha_458 & 0<=nc) & 2+
                                 na+nb+nc=flted_183_10780 & 3<=ha1_10782 & 
                                 (2+na+nb)<=flted_183_10780 & 2+
                                 ha=ha1_10782 & 0<=nb & 1<=na]
                               [res!=null][a!=null][0=color]
                               [0=flted_183_10781]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_184_10783,flted_184_10784,
                                 ha2_10785: res::rb<flted_184_10783,flted_184_10784,ha2_10785>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([Anon_20<=1 & 0<=Anon_20 & 
                                    (0<=flted_181_452 & flted_181_452<=1 & 
                                    1<=ha & 0<=na & 0<=Anon_19 & 
                                    Anon_19<=1 & 1<=ha_455 & 0<=nb & 
                                    0<=flted_181_451 & flted_181_451<=1 & 
                                    1<=ha_456 & 0<=nc | 0<=flted_182_454 & 
                                    flted_182_454<=1 & 1<=ha & 0<=na & 
                                    0<=Anon_20 & Anon_20<=1 & 1<=ha_457 & 
                                    0<=nb & 0<=flted_182_453 & 
                                    flted_182_453<=1 & 1<=ha_458 & 0<=nc) & 
                                    2+na+nb+nc=flted_184_10783 & 
                                    2<=ha2_10785 & (2+na+
                                    nb)<=flted_184_10783 & 1+ha=ha2_10785 & 
                                    0<=nb & 1<=na]
                                  [res!=null][a!=null][1=color]
                                  [1=flted_184_10784]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6r$node~node~node~int SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(bh,bh1)
!!! POST:  1=bh & 1=bh1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; Anon_21; 
                    bh](ex)x::rb<n,Anon_21,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=n][1<=bh][Anon_21<=1 & 0<=Anon_21]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 109::
                                EXISTS(flted_589_110,Anon_22,
                                bh1: res::rb<flted_589_110,Anon_22,bh1>@M[Orig][LHSCase]@ rem br[{697,696}]&
                                (
                                ([0!=flted_589_110 & 0<=flted_589_110 & -1+
                                   flted_589_110=n]
                                 [null!=res][1<=bh1 & INS(bh,bh1)]
                                 [Anon_22<=1 & 0<=Anon_22]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; Anon_21; 
                  bh](ex)x::rb<n,Anon_21,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][1<=bh][Anon_21<=1 & 0<=Anon_21]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 109::
                              EXISTS(flted_589_11578,Anon_11579,
                              bh1_11580: res::rb<flted_589_11578,Anon_11579,bh1_11580>@M[Orig][LHSCase]@ rem br[{697,696}]&
                              (
                              ([1=bh1_11580 & 1<=bh1_11580][bh=1 & 1<=bh]
                               [null!=res]
                               [0!=flted_589_11578 & 0<=n & -1+
                                 flted_589_11578=n & 0<=flted_589_11578]
                               [0<=Anon_11579 & Anon_11579<=1]
                               [Anon_21<=1 & 0<=Anon_21]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (bh=1 & bh1=1) --> INS(bh,bh1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure is_black$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; cl; 
                    bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=n][1<=bh][cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             x=null -> ((None,[]),EBase true&MayLoop&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 19::
                                                            true&(([res]))&
                                                            {FLOW,(20,21)=__norm})
                             ;
                             x!=null -> ((None,[]),EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 20::
                                                             
                                                             EXISTS(n_529,
                                                             cl_530,
                                                             bh1: x::rb<n_529,cl_530,bh1>@M[Orig][LHSCase]@ rem br[{697}]&
                                                             (
                                                             ([!(res)]
                                                              [n=n_529 & 
                                                                0<=n_529 & 
                                                                0!=n_529]
                                                              [cl=cl_530 & 
                                                                cl=1]
                                                              [1<=bh1]
                                                              [null!=x]))&
                                                             {FLOW,(20,21)=__norm})
                                                             or EXISTS(n_531,
                                                                cl_532,
                                                                bh2: 
                                                                x::rb<n_531,cl_532,bh2>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                                (
                                                                ([res]
                                                                 [n=n_531 & 
                                                                   0<=n_531]
                                                                 [cl=cl_532 & 
                                                                   cl=0]
                                                                 [1<=bh2]))&
                                                                {FLOW,(20,21)=__norm})
                                                             )
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; cl; 
                  bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][1<=bh][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 19::
                                                          true&(
                                                          ([null=x]
                                                           [0=n & 0<=n]
                                                           [1=bh & 1<=bh]
                                                           [0=cl & 0<=cl & 
                                                             cl<=1]
                                                           [res]))&
                                                          {FLOW,(20,21)=__norm})
                           ;
                           x!=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 20::
                                                           
                                                           EXISTS(n_11814,
                                                           cl_11815,
                                                           bh1_11816: 
                                                           x::rb<n_11814,cl_11815,bh1_11816>@M[Orig][LHSCase]@ rem br[{697}]&
                                                           (
                                                           ([n=n_11814 & 
                                                              1<=n & 0<=n]
                                                            [bh=bh1_11816 & 
                                                              1<=bh]
                                                            [x!=null]
                                                            [1=cl & 0<=cl & 
                                                              cl<=1]
                                                            [1=cl_11815]
                                                            [!(res)]))&
                                                           {FLOW,(20,21)=__norm})
                                                           or EXISTS(n_11817,
                                                              cl_11818,
                                                              bh2_11819: 
                                                              x::rb<n_11817,cl_11818,bh2_11819>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                              (
                                                              ([bh=bh2_11819 & 
                                                                 2<=bh & 
                                                                 1<=bh]
                                                               [x!=null]
                                                               [n=n_11817 & 
                                                                 1<=n & 0<=n]
                                                               [0=cl & 
                                                                 0<=cl & 
                                                                 cl<=1]
                                                               [0=cl_11818]
                                                               [res]))&
                                                              {FLOW,(20,21)=__norm})
                                                           )
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; cl; 
                    bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=n][1<=bh][cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             x=null -> ((None,[]),EBase true&MayLoop&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 14::
                                                            true&(
                                                            ([!(res)]))&
                                                            {FLOW,(20,21)=__norm})
                             ;
                             x!=null -> ((None,[]),EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 15::
                                                             
                                                             EXISTS(n_539,
                                                             cl_540,
                                                             bh1: x::rb<n_539,cl_540,bh1>@M[Orig][LHSCase]@ rem br[{697}]&
                                                             (
                                                             ([res]
                                                              [n=n_539 & 
                                                                0<=n_539 & 
                                                                0!=n_539]
                                                              [cl=cl_540 & 
                                                                cl=1]
                                                              [1<=bh1]
                                                              [null!=x]))&
                                                             {FLOW,(20,21)=__norm})
                                                             or EXISTS(n_541,
                                                                cl_542,
                                                                bh2: 
                                                                x::rb<n_541,cl_542,bh2>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                                (
                                                                ([!(res)]
                                                                 [n=n_541 & 
                                                                   0<=n_541]
                                                                 [cl=cl_542 & 
                                                                   cl=0]
                                                                 [1<=bh2]))&
                                                                {FLOW,(20,21)=__norm})
                                                             )
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; cl; 
                  bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][1<=bh][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 14::
                                                          true&(
                                                          ([null=x]
                                                           [0=n & 0<=n]
                                                           [1=bh & 1<=bh]
                                                           [0=cl & 0<=cl & 
                                                             cl<=1]
                                                           [!(res)]))&
                                                          {FLOW,(20,21)=__norm})
                           ;
                           x!=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 15::
                                                           
                                                           EXISTS(n_12053,
                                                           cl_12054,
                                                           bh1_12055: 
                                                           x::rb<n_12053,cl_12054,bh1_12055>@M[Orig][LHSCase]@ rem br[{697}]&
                                                           (
                                                           ([n=n_12053 & 
                                                              1<=n & 0<=n]
                                                            [bh=bh1_12055 & 
                                                              1<=bh]
                                                            [x!=null]
                                                            [1=cl & 0<=cl & 
                                                              cl<=1]
                                                            [1=cl_12054][
                                                            res]))&
                                                           {FLOW,(20,21)=__norm})
                                                           or EXISTS(n_12056,
                                                              cl_12057,
                                                              bh2_12058: 
                                                              x::rb<n_12056,cl_12057,bh2_12058>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                              (
                                                              ([x!=null]
                                                               [bh=bh2_12058 & 
                                                                 2<=bh & 
                                                                 1<=bh]
                                                               [n=n_12056 & 
                                                                 1<=n & 0<=n]
                                                               [0=cl & 
                                                                 0<=cl & 
                                                                 cl<=1]
                                                               [0=cl_12057]
                                                               [!(res)]))&
                                                              {FLOW,(20,21)=__norm})
                                                           )
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_red$node SUCCESS

Checking procedure remove_min$node... 
!!! REL :  RMVM1(bh,bh1)
!!! POST:  1=bh1 & 1=bh
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMVM1,RMVM2]
              EBase exists (Expl)(Impl)[n; cl; 
                    bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{697,696}]&
                    (([null!=x][0<=cl & cl<=1][1<=bh][0<=n & 0!=n]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 63::ref [x]
                                
                                EXISTS(flted_378_125,bh1,
                                cl2: x'::rb<flted_378_125,cl2,bh1>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                (
                                ([0<=flted_378_125 & 1+flted_378_125=n]
                                 [1<=bh1 & RMVM1(bh,bh1)][1=cl]
                                 [0<=cl2 & cl2<=1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_379_126,flted_379_127,
                                   bh2: x'::rb<flted_379_127,flted_379_126,bh2>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                   (
                                   ([0<=flted_379_127 & 1+flted_379_127=n]
                                    [0=flted_379_126]
                                    [1<=bh2 & bh2<=bh & (-1+bh)<=bh2][
                                    0=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; cl; 
                  bh](ex)x::rb<n,cl,bh>@M[Orig][LHSCase]@ rem br[{697,696}]&(
                  ([x!=null][1<=bh][1<=n][0<=cl & cl<=1]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 63::ref [x]
                              
                              EXISTS(flted_378_13501,bh1_13502,
                              cl2_13503: x'::rb<flted_378_13501,cl2_13503,bh1_13502>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                              (
                              ([bh=1 & 1<=bh][1=bh1_13502 & 1<=bh1_13502]
                               [0<=cl2_13503 & cl2_13503<=1]
                               [cl=1 & 0<=cl & cl<=1]
                               [0<=flted_378_13501 & 0<=n & 1+
                                 flted_378_13501=n]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_379_13504,flted_379_13505,
                                 bh2_13506: x'::rb<flted_379_13505,flted_379_13504,bh2_13506>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                 (
                                 ([cl=0 & 0<=cl & cl<=1]
                                  [1<=bh2_13506 & 1<=bh & (-1+
                                    bh)<=bh2_13506 & bh2_13506<=bh]
                                  [0=flted_379_13504]
                                  [0<=flted_379_13505 & 0<=n & 1+
                                    flted_379_13505=n]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (bh1=1 & bh=1) --> RMVM1(bh,bh1),
 (bh=1 & bh1=1) --> RMVM1(bh,bh1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; bha](ex)EXISTS(bha_652,
                    bha_653,flted_24_649,flted_24_650,
                    flted_24_651: a::rb<na,flted_24_651,bha>@M[Orig][LHSCase]@ rem br[{697}] * 
                    b::rb<nb,flted_24_650,bha_652>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_24_649,bha_653>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([flted_24_651=1][0=flted_24_650][0=flted_24_649]
                     [bha=bha_653 & bha=bha_652 & 1<=bha_653][0<=na & 0!=na]
                     [null!=a][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(flted_25_647,flted_25_648,
                                bha1: res::rb<flted_25_648,flted_25_647,bha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_25_648 & flted_25_648=2+na+nb+nc]
                                 [0=flted_25_647][1<=bha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  bha](ex)a::rb<na,flted_24_651,bha>@M[Orig][LHSCase]@ rem br[{697}] * 
                  b::rb<nb,flted_24_650,bha_652>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_24_649,bha_653>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([bha_652=bha & bha_652=bha_653 & 1<=bha_652][1<=na]
                   [a!=null][0<=nb][0<=nc][1=flted_24_651][0=flted_24_650]
                   [0=flted_24_649]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(flted_25_13635,flted_25_13636,
                              bha1_13637: res::rb<flted_25_13635,flted_25_13636,bha1_13637>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([1+bha=bha1_13637 & 1<=bha & 2<=bha1_13637]
                               [2+na+nb+nc=flted_25_13635 & 0<=na & (3+nb+
                                 nc)<=flted_25_13635 & 0<=nb & 0<=nc]
                               [a!=null][res!=null][0=flted_25_13636]
                               [1<=bha_653]
                               [0<=flted_24_649 & flted_24_649<=1]
                               [1<=bha_652]
                               [0<=flted_24_650 & flted_24_650<=1]
                               [0<=flted_24_651 & flted_24_651<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; bha](ex)EXISTS(bha_592,
                    bha_593,flted_66_589,flted_66_590,
                    flted_66_591: a::rb<na,flted_66_591,bha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb<nb,flted_66_590,bha_592>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb<nc,flted_66_589,bha_593>@M[Orig][LHSCase]@ rem br[{697}]&
                    (
                    ([0=flted_66_591][0=flted_66_590][flted_66_589=1]
                     [bha=bha_593 & bha=bha_592 & 1<=bha_593][0<=na][
                     0<=nb][0<=nc & 0!=nc][null!=c]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_67_587,flted_67_588,
                                bha1: res::rb<flted_67_588,flted_67_587,bha1>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (
                                ([0<=flted_67_588 & flted_67_588=2+na+nb+nc]
                                 [0=flted_67_587][1<=bha1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  bha](ex)a::rb<na,flted_66_591,bha>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb<nb,flted_66_590,bha_592>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb<nc,flted_66_589,bha_593>@M[Orig][LHSCase]@ rem br[{697}]&
                  (
                  ([bha_592=bha & bha_592=bha_593 & 1<=bha_592][0<=na][
                   0<=nb][1<=nc][c!=null][0=flted_66_591][0=flted_66_590]
                   [1=flted_66_589]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(flted_67_13766,flted_67_13767,
                              bha1_13768: res::rb<flted_67_13766,flted_67_13767,bha1_13768>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([1+bha=bha1_13768 & 1<=bha & 2<=bha1_13768]
                               [2+na+nb+nc=flted_67_13766 & (2+na+
                                 nc)<=flted_67_13766 & 0<=nb & 0<=na & 
                                 0<=nc & 1<=nc]
                               [c!=null][res!=null][0=flted_67_13767]
                               [1<=bha_593]
                               [0<=flted_66_589 & flted_66_589<=1]
                               [1<=bha_592]
                               [0<=flted_66_590 & flted_66_590<=1]
                               [0<=flted_66_591 & flted_66_591<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 5805 invocations 
324 false contexts at: ( (452,3)  (452,10)  (449,4)  (449,11)  (444,22)  (444,29)  (443,26)  (443,71)  (443,56)  (443,42)  (443,34)  (443,22)  (443,22)  (438,26)  (438,33)  (437,30)  (437,100)  (437,85)  (437,65)  (437,46)  (437,38)  (437,26)  (437,26)  (433,28)  (433,35)  (432,32)  (432,62)  (432,48)  (432,40)  (432,28)  (432,28)  (428,28)  (428,35)  (427,32)  (427,62)  (427,48)  (427,40)  (427,28)  (427,28)  (425,39)  (425,28)  (425,28)  (425,24)  (424,37)  (424,26)  (424,22)  (422,33)  (422,22)  (422,18)  (418,20)  (418,27)  (415,22)  (415,29)  (414,26)  (414,56)  (414,42)  (414,34)  (414,22)  (414,22)  (412,22)  (412,22)  (412,18)  (410,27)  (410,18)  (410,14)  (408,25)  (408,14)  (408,10)  (406,6)  (406,22)  (406,19)  (116,2)  (116,9)  (121,3)  (121,10)  (119,3)  (119,10)  (118,17)  (118,6)  (118,6)  (118,2)  (142,2)  (142,9)  (147,3)  (147,10)  (145,3)  (145,10)  (144,17)  (144,6)  (144,6)  (144,2)  (696,14)  (693,16)  (689,24)  (686,28)  (686,35)  (685,32)  (685,71)  (685,57)  (685,49)  (685,28)  (685,28)  (681,28)  (681,35)  (680,44)  (680,28)  (679,43)  (679,28)  (679,28)  (677,37)  (677,28)  (677,24)  (672,24)  (672,31)  (671,28)  (671,85)  (671,65)  (671,46)  (671,38)  (671,24)  (671,24)  (667,24)  (667,31)  (666,40)  (666,24)  (665,39)  (665,24)  (665,24)  (663,33)  (663,24)  (663,20)  (650,12)  (647,16)  (643,24)  (639,30)  (639,37)  (638,34)  (638,95)  (638,75)  (638,56)  (638,43)  (638,30)  (638,30)  (634,30)  (634,37)  (633,46)  (633,30)  (632,45)  (632,30)  (632,30)  (630,39)  (630,30)  (630,26)  (623,26)  (623,33)  (622,30)  (622,73)  (622,59)  (622,46)  (622,26)  (622,26)  (618,26)  (618,33)  (617,42)  (617,26)  (616,41)  (616,26)  (616,26)  (614,35)  (614,26)  (614,22)  (554,14)  (575,30)  (575,75)  (575,60)  (575,46)  (575,38)  (575,26)  (573,32)  (573,102)  (573,87)  (573,67)  (573,48)  (573,40)  (573,28)  (570,36)  (570,66)  (570,52)  (570,44)  (570,32)  (568,36)  (568,66)  (568,52)  (568,44)  (568,32)  (567,45)  (567,34)  (567,34)  (567,30)  (565,41)  (565,30)  (565,26)  (564,39)  (564,28)  (564,24)  (560,30)  (560,60)  (560,46)  (560,38)  (560,26)  (559,28)  (559,28)  (559,24)  (557,33)  (557,24)  (557,20)  (556,33)  (556,22)  (556,18)  (554,18)  (554,34)  (554,31)  (527,14)  (546,34)  (546,79)  (546,70)  (546,56)  (546,43)  (546,30)  (544,32)  (544,102)  (544,93)  (544,73)  (544,54)  (544,41)  (544,28)  (542,34)  (542,70)  (542,56)  (542,43)  (542,30)  (540,34)  (540,70)  (540,56)  (540,43)  (540,30)  (539,43)  (539,32)  (539,32)  (539,28)  (538,41)  (538,30)  (538,26)  (537,39)  (537,28)  (537,24)  (533,30)  (533,66)  (533,52)  (533,39)  (533,26)  (532,28)  (532,28)  (532,24)  (530,33)  (530,24)  (530,20)  (529,33)  (529,22)  (529,18)  (527,18)  (527,35)  (527,32)  (494,14)  (514,32)  (514,77)  (514,68)  (514,54)  (514,41)  (514,28)  (512,34)  (512,104)  (512,95)  (512,75)  (512,56)  (512,43)  (512,30)  (510,36)  (510,72)  (510,58)  (510,45)  (510,32)  (508,36)  (508,72)  (508,58)  (508,45)  (508,32)  (507,45)  (507,34)  (507,34)  (507,30)  (506,43)  (506,32)  (506,28)  (505,41)  (505,30)  (505,26)  (501,32)  (501,68)  (501,54)  (501,41)  (501,28)  (500,30)  (500,30)  (500,26)  (498,35)  (498,26)  (498,22)  (496,33)  (496,22)  (496,18)  (494,18)  (494,35)  (494,32) )

Total verification time: 5.56 second(s)
	Time spent in main process: 4. second(s)
	Time spent in child processes: 1.56 second(s)
