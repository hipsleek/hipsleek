
Processing file "rb_ms.ss"
Parsing rb_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure case_2$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)EXISTS(flted_45_449,flted_45_450,flted_45_451,
                    flted_45_452: a::rb2<na,flted_45_452>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_45_451>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_45_450>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    d::rb2<nd,flted_45_449>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_45_452][0=flted_45_451][0=flted_45_450]
                     [0=flted_45_449][0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(flted_46_448,
                                n: res::rb2<n,flted_46_448>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_46_448][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)a::rb2<na,flted_45_452>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_45_451>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_45_450>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  d::rb2<nd,flted_45_449>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_45_452]
                   [0=flted_45_451][0=flted_45_450][0=flted_45_449]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(n_3601,
                              flted_46_3602: res::rb2<n_3601,flted_46_3602>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([3+na+nb+nc+nd=n_3601 & (3+na+nc+
                                 nd)<=n_3601 & 0<=nb & 0<=na & 0<=nd & 0<=nc]
                               [res!=null][0=flted_46_3602]
                               [0<=flted_45_449 & flted_45_449<=1]
                               [0<=flted_45_450 & flted_45_450<=1]
                               [0<=flted_45_451 & flted_45_451<=1]
                               [0<=flted_45_452 & flted_45_452<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)EXISTS(flted_87_407,flted_87_408,flted_87_409,
                    flted_87_410: a::rb2<na,flted_87_410>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_87_409>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_87_408>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    d::rb2<nd,flted_87_407>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_87_410][0=flted_87_409][0=flted_87_408]
                     [0=flted_87_407][0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(flted_88_406,
                                n: res::rb2<n,flted_88_406>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_88_406][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)a::rb2<na,flted_87_410>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_87_409>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_87_408>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  d::rb2<nd,flted_87_407>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_87_410]
                   [0=flted_87_409][0=flted_87_408][0=flted_87_407]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(n_3697,
                              flted_88_3698: res::rb2<n_3697,flted_88_3698>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([res!=null]
                               [3+na+nb+nc+nd=n_3697 & (3+na+nb+
                                 nc)<=n_3697 & 0<=nc & 0<=nb & 0<=nd & 0<=na]
                               [0=flted_88_3698]
                               [0<=flted_87_407 & flted_87_407<=1]
                               [0<=flted_87_408 & flted_87_408<=1]
                               [0<=flted_87_409 & flted_87_409<=1]
                               [0<=flted_87_410 & flted_87_410<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure del_2r$node~node~node... 
Procedure del_2r$node~node~node SUCCESS

Checking procedure del$node~int... 
!!! REL :  DEL2(n,n2)
!!! POST:  n2>=0 & (n2+1)>=n & n>=n2
!!! PRE :  true
!!! REL :  DEL1(n,n1)
!!! POST:  n1>=0 & n1+1=n
!!! PRE :  true
!!! REL :  DEL3(n,n3)
!!! POST:  n3>=0 & (n3+1)>=n & n>=n3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL1,DEL2,DEL3]
              EBase exists (Expl)(Impl)[n; 
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=cl & cl<=1][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::ref [x]
                                
                                EXISTS(cl2,
                                n1: x'::rb2<n1,cl2>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                (
                                ([1=cl][0<=cl2 & cl2<=1][0<=n1 & DEL1(n,n1)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_506_112,
                                   n2: x'::rb2<n2,flted_506_112>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                   (
                                   ([0=flted_506_112][0=cl]
                                    [0<=n2 & DEL2(n,n2)]))&
                                   {FLOW,(20,21)=__norm})
                                or EXISTS(cl_113,
                                   n3: x'::rb2<n3,cl_113>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                   (
                                   ([0<=n3 & DEL3(n,n3)]
                                    [cl=cl_113 & cl_113<=1 & 0<=cl_113]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::ref [x]
                              
                              EXISTS(flted_506_5384,
                              n2_5385: x'::rb2<n2_5385,flted_506_5384>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([n2_5385<=n & 0<=n & 0<=n2_5385 & (-1+
                                 n)<=n2_5385]
                               [cl=0 & 0<=cl & cl<=1][0=flted_506_5384]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl2_5386,
                                 n1_5387: x'::rb2<n1_5387,cl2_5386>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                 (
                                 ([1+n1_5387=n & 0<=n & 0<=n1_5387]
                                  [0<=cl2_5386 & cl2_5386<=1]
                                  [cl=1 & 0<=cl & cl<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(cl_5388,
                                 n3_5389: x'::rb2<n3_5389,cl_5388>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                 (
                                 ([n3_5389<=n & 0<=n & 0<=n3_5389 & (-1+
                                    n)<=n3_5389]
                                  [cl=cl_5388 & cl<=1 & 0<=cl]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (n2=n-1 & 2<=n) --> DEL2(n,n2),
 (n2=n-1 & 1<=n) --> DEL2(n,n2),
 (n2=0 & n=0) --> DEL2(n,n2),
 (n3=n-1 & 2<=n) --> DEL3(n,n3),
 (n1=n-1 & 1<=n) --> DEL1(n,n1),
 (n3=n-1 & 1<=n) --> DEL3(n,n3),
 (n3=0 & n=0) --> DEL3(n,n3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$node~int SUCCESS

Checking procedure del_2$node~node~node... 
Procedure del_2$node~node~node SUCCESS

Checking procedure del_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_301_188,
                    flted_301_189,
                    flted_301_190: a::rb2<na,flted_301_190>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_301_189>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_301_188>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_301_190][0=flted_301_189][0=flted_301_188]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(flted_302_187,
                                n: res::rb2<n,flted_302_187>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_302_187][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_301_190>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_301_189>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_301_188>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_301_190][0=flted_301_189]
                   [0=flted_301_188]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(n_5973,
                              flted_302_5974: res::rb2<n_5973,flted_302_5974>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=n_5973 & 0<=na & (2+nb+
                                 nc)<=n_5973 & 0<=nb & 0<=nc]
                               [res!=null][0=flted_302_5974]
                               [0<=flted_301_188 & flted_301_188<=1]
                               [0<=flted_301_189 & flted_301_189<=1]
                               [0<=flted_301_190 & flted_301_190<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_321_169,
                    flted_321_170,
                    flted_321_171: a::rb2<na,flted_321_171>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_321_170>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_321_169>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_321_171][0=flted_321_170][0=flted_321_169]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(flted_322_168,
                                n: res::rb2<n,flted_322_168>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_322_168][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_321_171>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_321_170>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_321_169>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_321_171][0=flted_321_170]
                   [0=flted_321_169]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(n_6088,
                              flted_322_6089: res::rb2<n_6088,flted_322_6089>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=n_6088 & (2+na+nc)<=n_6088 & 
                                 0<=nb & 0<=nc & 0<=na]
                               [res!=null][0=flted_322_6089]
                               [0<=flted_321_169 & flted_321_169<=1]
                               [0<=flted_321_170 & flted_321_170<=1]
                               [0<=flted_321_171 & flted_321_171<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_262_226,
                    flted_262_227,
                    flted_262_228: a::rb2<na,flted_262_228>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_262_227>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_262_226>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_262_228][0=flted_262_227][0=flted_262_226]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_263_225,
                                n: res::rb2<n,flted_263_225>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_263_225][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_262_228>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_262_227>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_262_226>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_262_228][0=flted_262_227]
                   [0=flted_262_226]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(n_6211,
                              flted_263_6212: res::rb2<n_6211,flted_263_6212>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=n_6211 & (2+na+nc)<=n_6211 & 
                                 0<=nb & 0<=na & 0<=nc]
                               [res!=null][0=flted_263_6212]
                               [0<=flted_262_226 & flted_262_226<=1]
                               [0<=flted_262_227 & flted_262_227<=1]
                               [0<=flted_262_228 & flted_262_228<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_281_207,
                    flted_281_208,
                    flted_281_209: a::rb2<na,flted_281_209>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_281_208>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_281_207>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([0=flted_281_209][0=flted_281_208][0=flted_281_207]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                EXISTS(flted_282_206,
                                n: res::rb2<n,flted_282_206>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_282_206][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_281_209>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_281_208>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_281_207>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_281_209][0=flted_281_208]
                   [0=flted_281_207]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              EXISTS(n_6326,
                              flted_282_6327: res::rb2<n_6326,flted_282_6327>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=n_6326 & (2+na+nc)<=n_6326 & 
                                 0<=nb & 0<=nc & 0<=na]
                               [res!=null][0=flted_282_6327]
                               [0<=flted_281_207 & flted_281_207<=1]
                               [0<=flted_281_208 & flted_281_208<=1]
                               [0<=flted_281_209 & flted_281_209<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)
                           EXISTS(flted_215_298,flted_215_299,flted_215_300,
                           flted_215_301: a::rb2<na,flted_215_301>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           b::rb2<nb,flted_215_300>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           c::rb2<nc,flted_215_299>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           d::rb2<nd,flted_215_298>@M[Orig][LHSCase]@ rem br[{698,696}]&
                           (
                           ([0=flted_215_301][0=flted_215_300]
                            [0=flted_215_299][0=flted_215_298][0=color]
                            [0<=na][0<=nb][0<=nc][0<=nd]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_216_302,flted_216_303,
                              flted_216_304,
                              flted_216_305: a::rb2<na,flted_216_305>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              b::rb2<nb,flted_216_304>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              c::rb2<nc,flted_216_303>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              d::rb2<nd,flted_216_302>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([0=flted_216_305][0=flted_216_304]
                               [0=flted_216_303][0=flted_216_302][1=color]
                               [0<=na][0<=nb][0<=nc][0<=nd]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 32::
                                
                                EXISTS(flted_217_296,
                                n1: res::rb2<n1,flted_217_296>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_217_296][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_218_297,
                                   n2: res::rb2<n2,flted_218_297>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([flted_218_297=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)
                         a::rb2<na,flted_215_301>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         b::rb2<nb,flted_215_300>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         c::rb2<nc,flted_215_299>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         d::rb2<nd,flted_215_298>@M[Orig][LHSCase]@ rem br[{698,696}]&
                         (
                         ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_215_301]
                          [0=flted_215_300][0=flted_215_299][0=flted_215_298]
                          [0=color]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_216_305>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            b::rb2<nb,flted_216_304>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            c::rb2<nc,flted_216_303>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            d::rb2<nd,flted_216_302>@M[Orig][LHSCase]@ rem br[{698,696}]&
                            (
                            ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_216_305]
                             [0=flted_216_304][0=flted_216_303]
                             [0=flted_216_302][1=color]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 32::
                              
                              EXISTS(n1_6623,
                              flted_217_6624: res::rb2<n1_6623,flted_217_6624>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([(0<=flted_215_301 & flted_215_301<=1 & 
                                 0<=na & 0<=flted_215_300 & 
                                 flted_215_300<=1 & 0<=nb & 
                                 0<=flted_215_299 & flted_215_299<=1 & 
                                 0<=nc & 0<=flted_215_298 & 
                                 flted_215_298<=1 & 0<=nd | 
                                 0<=flted_216_305 & flted_216_305<=1 & 
                                 0<=na & 0<=flted_216_304 & 
                                 flted_216_304<=1 & 0<=nb & 
                                 0<=flted_216_303 & flted_216_303<=1 & 
                                 0<=nc & 0<=flted_216_302 & 
                                 flted_216_302<=1 & 0<=nd) & n1_6623=3+na+nb+
                                 nc+nd & 0<=nd & 0<=na & 0<=nb & 0<=nc]
                               [res!=null][0=flted_217_6624][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_6625,
                                 flted_218_6626: res::rb2<n2_6625,flted_218_6626>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([(0<=flted_215_301 & flted_215_301<=1 & 
                                    0<=na & 0<=flted_215_300 & 
                                    flted_215_300<=1 & 0<=nb & 
                                    0<=flted_215_299 & flted_215_299<=1 & 
                                    0<=nc & 0<=flted_215_298 & 
                                    flted_215_298<=1 & 0<=nd | 
                                    0<=flted_216_305 & flted_216_305<=1 & 
                                    0<=na & 0<=flted_216_304 & 
                                    flted_216_304<=1 & 0<=nb & 
                                    0<=flted_216_303 & flted_216_303<=1 & 
                                    0<=nc & 0<=flted_216_302 & 
                                    flted_216_302<=1 & 0<=nd) & n2_6625=3+na+
                                    nb+nc+nd & 0<=nb & 0<=na & 0<=nd & 0<=nc]
                                  [res!=null][1=flted_218_6626][1=color]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5$node~node~node~node~int SUCCESS

Checking procedure del_5r$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)
                           EXISTS(flted_240_253,flted_240_254,flted_240_255,
                           flted_240_256: a::rb2<na,flted_240_256>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           b::rb2<nb,flted_240_255>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           c::rb2<nc,flted_240_254>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           d::rb2<nd,flted_240_253>@M[Orig][LHSCase]@ rem br[{698,696}]&
                           (
                           ([0=flted_240_256][0=flted_240_255]
                            [0=flted_240_254][0=flted_240_253][0=color]
                            [0<=na][0<=nb][0<=nc][0<=nd]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_241_257,flted_241_258,
                              flted_241_259,
                              flted_241_260: a::rb2<na,flted_241_260>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              b::rb2<nb,flted_241_259>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              c::rb2<nc,flted_241_258>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              d::rb2<nd,flted_241_257>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([0=flted_241_260][0=flted_241_259]
                               [0=flted_241_258][0=flted_241_257][1=color]
                               [0<=na][0<=nb][0<=nc][0<=nd]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                
                                EXISTS(flted_242_251,
                                n1: res::rb2<n1,flted_242_251>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_242_251][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_243_252,
                                   n2: res::rb2<n2,flted_243_252>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([flted_243_252=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)
                         a::rb2<na,flted_240_256>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         b::rb2<nb,flted_240_255>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         c::rb2<nc,flted_240_254>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         d::rb2<nd,flted_240_253>@M[Orig][LHSCase]@ rem br[{698,696}]&
                         (
                         ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_240_256]
                          [0=flted_240_255][0=flted_240_254][0=flted_240_253]
                          [0=color]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_241_260>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            b::rb2<nb,flted_241_259>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            c::rb2<nc,flted_241_258>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            d::rb2<nd,flted_241_257>@M[Orig][LHSCase]@ rem br[{698,696}]&
                            (
                            ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_241_260]
                             [0=flted_241_259][0=flted_241_258]
                             [0=flted_241_257][1=color]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              
                              EXISTS(n1_6930,
                              flted_242_6931: res::rb2<n1_6930,flted_242_6931>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([(0<=flted_240_256 & flted_240_256<=1 & 
                                 0<=na & 0<=flted_240_255 & 
                                 flted_240_255<=1 & 0<=nb & 
                                 0<=flted_240_254 & flted_240_254<=1 & 
                                 0<=nc & 0<=flted_240_253 & 
                                 flted_240_253<=1 & 0<=nd | 
                                 0<=flted_241_260 & flted_241_260<=1 & 
                                 0<=na & 0<=flted_241_259 & 
                                 flted_241_259<=1 & 0<=nb & 
                                 0<=flted_241_258 & flted_241_258<=1 & 
                                 0<=nc & 0<=flted_241_257 & 
                                 flted_241_257<=1 & 0<=nd) & n1_6930=3+na+nb+
                                 nc+nd & 0<=na & 0<=nc & 0<=nb & 0<=nd]
                               [res!=null][0=flted_242_6931][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_6932,
                                 flted_243_6933: res::rb2<n2_6932,flted_243_6933>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([res!=null]
                                  [(0<=flted_240_256 & flted_240_256<=1 & 
                                    0<=na & 0<=flted_240_255 & 
                                    flted_240_255<=1 & 0<=nb & 
                                    0<=flted_240_254 & flted_240_254<=1 & 
                                    0<=nc & 0<=flted_240_253 & 
                                    flted_240_253<=1 & 0<=nd | 
                                    0<=flted_241_260 & flted_241_260<=1 & 
                                    0<=na & 0<=flted_241_259 & 
                                    flted_241_259<=1 & 0<=nb & 
                                    0<=flted_241_258 & flted_241_258<=1 & 
                                    0<=nc & 0<=flted_241_257 & 
                                    flted_241_257<=1 & 0<=nd) & n2_6932=3+na+
                                    nb+nc+nd & 0<=na & 0<=nb & 0<=nc & 0<=nd]
                                  [1=flted_243_6933][1=color]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5r$node~node~node~node~int SUCCESS

Checking procedure del_6$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; 
                    nc](ex)
                           EXISTS(flted_161_368,
                           flted_161_369: a::rb2<na,flted_161_369>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                           b::rb2<nb,Anon_15>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                           c::rb2<nc,flted_161_368>@M[Orig][LHSCase]@ rem br[{697}]&
                           (
                           ([0=flted_161_369][flted_161_368=1][0=color]
                            [null!=c][0<=na][0<=nb][Anon_15<=1 & 0<=Anon_15]
                            [0<=nc & 0!=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_162_370,
                              flted_162_371: a::rb2<na,flted_162_371>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                              b::rb2<nb,Anon_16>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                              c::rb2<nc,flted_162_370>@M[Orig][LHSCase]@ rem br[{697}]&
                              (
                              ([0=flted_162_371][flted_162_370=1][1=color]
                               [null!=c][0<=na][0<=nb]
                               [Anon_16<=1 & 0<=Anon_16][0<=nc & 0!=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 24::
                                
                                EXISTS(flted_163_366,
                                n1: res::rb2<n1,flted_163_366>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_163_366][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_164_367,
                                   n2: res::rb2<n2,flted_164_367>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([flted_164_367=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; 
                  nc](ex)
                         a::rb2<na,flted_161_369>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                         b::rb2<nb,Anon_15>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                         c::rb2<nc,flted_161_368>@M[Orig][LHSCase]@ rem br[{697}]&
                         (
                         ([c!=null][0<=na][0<=nb][1<=nc][0=flted_161_369]
                          [1=flted_161_368][0=color][Anon_15<=1 & 0<=Anon_15]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_162_371>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                            b::rb2<nb,Anon_16>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                            c::rb2<nc,flted_162_370>@M[Orig][LHSCase]@ rem br[{697}]&
                            (
                            ([c!=null][0<=na][0<=nb][1<=nc][0=flted_162_371]
                             [1=flted_162_370][1=color]
                             [Anon_16<=1 & 0<=Anon_16]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 24::
                              
                              EXISTS(n1_7440,
                              flted_163_7441: res::rb2<n1_7440,flted_163_7441>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_161_369 & flted_161_369<=1 & 
                                 0<=na & 0<=Anon_15 & Anon_15<=1 & 0<=nb & 
                                 0<=flted_161_368 & flted_161_368<=1 & 
                                 0<=nc | 0<=flted_162_371 & 
                                 flted_162_371<=1 & 0<=na & 0<=Anon_16 & 
                                 Anon_16<=1 & 0<=nb & 0<=flted_162_370 & 
                                 flted_162_370<=1 & 0<=nc) & 2+na+nb+
                                 nc=n1_7440 & 1<=nc & (2+nb+nc)<=n1_7440 & 
                                 0<=nb]
                               [res!=null][c!=null][0=color]
                               [0=flted_163_7441]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_7442,
                                 flted_164_7443: res::rb2<n2_7442,flted_164_7443>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([Anon_16<=1 & 0<=Anon_16 & 
                                    (0<=flted_161_369 & flted_161_369<=1 & 
                                    0<=na & 0<=Anon_15 & Anon_15<=1 & 
                                    0<=nb & 0<=flted_161_368 & 
                                    flted_161_368<=1 & 0<=nc | 
                                    0<=flted_162_371 & flted_162_371<=1 & 
                                    0<=na & 0<=Anon_16 & Anon_16<=1 & 
                                    0<=nb & 0<=flted_162_370 & 
                                    flted_162_370<=1 & 0<=nc) & 2+na+nb+
                                    nc=n2_7442 & 1<=nc & (2+nb+
                                    nc)<=n2_7442 & 0<=nb]
                                  [res!=null][c!=null][1=color]
                                  [1=flted_164_7443]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6$node~node~node~int SUCCESS

Checking procedure del_6r$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; 
                    nc](ex)
                           EXISTS(flted_188_339,
                           flted_188_340: a::rb2<na,flted_188_340>@M[Orig][LHSCase]@ rem br[{697}] * 
                           b::rb2<nb,Anon_19>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                           c::rb2<nc,flted_188_339>@M[Orig][LHSCase]@ rem br[{698,696}]&
                           (
                           ([flted_188_340=1][0=flted_188_339][0=color]
                            [null!=a][0<=na & 0!=na][0<=nb]
                            [Anon_19<=1 & 0<=Anon_19][0<=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_189_341,
                              flted_189_342: a::rb2<na,flted_189_342>@M[Orig][LHSCase]@ rem br[{697}] * 
                              b::rb2<nb,Anon_20>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                              c::rb2<nc,flted_189_341>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([flted_189_342=1][0=flted_189_341][1=color]
                               [null!=a][0<=na & 0!=na][0<=nb]
                               [Anon_20<=1 & 0<=Anon_20][0<=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                
                                EXISTS(flted_190_337,
                                n1: res::rb2<n1,flted_190_337>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_190_337][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_191_338,
                                   n2: res::rb2<n2,flted_191_338>@M[Orig][LHSCase]@ rem br[{697}]&
                                   (
                                   ([flted_191_338=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; 
                  nc](ex)
                         a::rb2<na,flted_188_340>@M[Orig][LHSCase]@ rem br[{697}] * 
                         b::rb2<nb,Anon_19>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                         c::rb2<nc,flted_188_339>@M[Orig][LHSCase]@ rem br[{698,696}]&
                         (
                         ([a!=null][1<=na][0<=nb][0<=nc][1=flted_188_340]
                          [0=flted_188_339][0=color][Anon_19<=1 & 0<=Anon_19]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_189_342>@M[Orig][LHSCase]@ rem br[{697}] * 
                            b::rb2<nb,Anon_20>@M[Orig][LHSCase]@ rem br[{698,697,696}] * 
                            c::rb2<nc,flted_189_341>@M[Orig][LHSCase]@ rem br[{698,696}]&
                            (
                            ([a!=null][1<=na][0<=nb][0<=nc][1=flted_189_342]
                             [0=flted_189_341][1=color]
                             [Anon_20<=1 & 0<=Anon_20]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              
                              EXISTS(n1_7966,
                              flted_190_7967: res::rb2<n1_7966,flted_190_7967>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_188_340 & flted_188_340<=1 & 
                                 0<=na & 0<=Anon_19 & Anon_19<=1 & 0<=nb & 
                                 0<=flted_188_339 & flted_188_339<=1 & 
                                 0<=nc | 0<=flted_189_342 & 
                                 flted_189_342<=1 & 0<=na & 0<=Anon_20 & 
                                 Anon_20<=1 & 0<=nb & 0<=flted_189_341 & 
                                 flted_189_341<=1 & 0<=nc) & 2+na+nb+
                                 nc=n1_7966 & 1<=na & (2+na+nb)<=n1_7966 & 
                                 0<=nb]
                               [res!=null][a!=null][0=color]
                               [0=flted_190_7967]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_7968,
                                 flted_191_7969: res::rb2<n2_7968,flted_191_7969>@M[Orig][LHSCase]@ rem br[{697}]&
                                 (
                                 ([Anon_20<=1 & 0<=Anon_20 & 
                                    (0<=flted_188_340 & flted_188_340<=1 & 
                                    0<=na & 0<=Anon_19 & Anon_19<=1 & 
                                    0<=nb & 0<=flted_188_339 & 
                                    flted_188_339<=1 & 0<=nc | 
                                    0<=flted_189_342 & flted_189_342<=1 & 
                                    0<=na & 0<=Anon_20 & Anon_20<=1 & 
                                    0<=nb & 0<=flted_189_341 & 
                                    flted_189_341<=1 & 0<=nc) & 2+na+nb+
                                    nc=n2_7968 & 1<=na & (2+na+
                                    nb)<=n2_7968 & 0<=nb]
                                  [res!=null][a!=null][1=color]
                                  [1=flted_191_7969]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6r$node~node~node~int SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(n,n1)
!!! POST:  0=n & 1=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; 
                    Anon_21](ex)x::rb2<n,Anon_21>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=n][Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 109::
                                EXISTS(Anon_22,
                                n1: res::rb2<n1,Anon_22>@M[Orig][LHSCase]@ rem br[{697,696}]&
                                (
                                ([null!=res][0!=n1 & 0<=n1 & INS(n,n1)]
                                 [Anon_22<=1 & 0<=Anon_22]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  Anon_21](ex)x::rb2<n,Anon_21>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 109::
                              EXISTS(Anon_8664,
                              n1_8665: res::rb2<n1_8665,Anon_8664>@M[Orig][LHSCase]@ rem br[{697,696}]&
                              (
                              ([1=n1_8665 & 0!=n1_8665 & 0<=n1_8665]
                               [n=0 & 0<=n][null!=res]
                               [0<=Anon_8664 & Anon_8664<=1]
                               [Anon_21<=1 & 0<=Anon_21]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & n1=1) --> INS(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure is_black$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              ECase case {
                     x=null -> ((None,[]),EBase true&MayLoop&
                                                {FLOW,(1,23)=__flow}
                                                  EAssume 19::
                                                    true&(([res]))&
                                                    {FLOW,(20,21)=__norm})
                     ;
                     x!=null -> ((None,[]),EBase exists (Expl)(Impl)[n; 
                                                 cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                                 (([0<=n][cl<=1 & 0<=cl]))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 20::
                                                             
                                                             EXISTS(cl_389,
                                                             n1: x::rb2<n1,cl_389>@M[Orig][LHSCase]@ rem br[{697}]&
                                                             (
                                                             ([!(res)]
                                                              [cl=cl_389 & 
                                                                cl=1]
                                                              [0<=n1 & 0!=n1]
                                                              [null!=x]))&
                                                             {FLOW,(20,21)=__norm})
                                                             or EXISTS(cl_390,
                                                                n2: x::rb2<n2,cl_390>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                                (
                                                                ([res]
                                                                 [cl=cl_390 & 
                                                                   cl=0]
                                                                 [0<=n2]))&
                                                                {FLOW,(20,21)=__norm})
                                                             )
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                              {FLOW,(1,23)=__flow}
                                                EAssume 19::
                                                  true&(([null=x][res]))&
                                                  {FLOW,(20,21)=__norm})
                   ;
                   x!=null -> ((None,[]),EBase exists (Expl)(Impl)[n; 
                                               cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                               (([0<=n][0<=cl & cl<=1]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 20::
                                                           
                                                           EXISTS(n1_8862,
                                                           cl_8863: x::rb2<n1_8862,cl_8863>@M[Orig][LHSCase]@ rem br[{697}]&
                                                           (
                                                           ([n=n1_8862 & 
                                                              1<=n1_8862 & 
                                                              0<=n]
                                                            [x!=null]
                                                            [1=cl & 0<=cl & 
                                                              cl<=1]
                                                            [1=cl_8863]
                                                            [!(res)]))&
                                                           {FLOW,(20,21)=__norm})
                                                           or EXISTS(n2_8864,
                                                              cl_8865: 
                                                              x::rb2<n2_8864,cl_8865>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                              (
                                                              ([n=n2_8864 & 
                                                                 1<=n & 0<=n]
                                                               [x!=null]
                                                               [0=cl & 
                                                                 0<=cl & 
                                                                 cl<=1]
                                                               [0=cl_8865]
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
              EBase exists (Expl)(Impl)[n; 
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                    (([0<=n][cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
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
                                                             
                                                             EXISTS(cl_395,
                                                             n1: x::rb2<n1,cl_395>@M[Orig][LHSCase]@ rem br[{697}]&
                                                             (
                                                             ([res]
                                                              [cl=cl_395 & 
                                                                cl=1]
                                                              [0<=n1 & 0!=n1]
                                                              [null!=x]))&
                                                             {FLOW,(20,21)=__norm})
                                                             or EXISTS(cl_396,
                                                                n2: x::rb2<n2,cl_396>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                                (
                                                                ([!(res)]
                                                                 [cl=cl_396 & 
                                                                   cl=0]
                                                                 [0<=n2]))&
                                                                {FLOW,(20,21)=__norm})
                                                             )
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                  (([0<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 14::
                                                          true&(
                                                          ([null=x]
                                                           [0=n & 0<=n]
                                                           [0=cl & 0<=cl & 
                                                             cl<=1]
                                                           [!(res)]))&
                                                          {FLOW,(20,21)=__norm})
                           ;
                           x!=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 15::
                                                           
                                                           EXISTS(n1_9062,
                                                           cl_9063: x::rb2<n1_9062,cl_9063>@M[Orig][LHSCase]@ rem br[{697}]&
                                                           (
                                                           ([n=n1_9062 & 
                                                              1<=n1_9062 & 
                                                              0<=n]
                                                            [x!=null]
                                                            [1=cl & 0<=cl & 
                                                              cl<=1]
                                                            [1=cl_9063][
                                                            res]))&
                                                           {FLOW,(20,21)=__norm})
                                                           or EXISTS(n2_9064,
                                                              cl_9065: 
                                                              x::rb2<n2_9064,cl_9065>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                                              (
                                                              ([x!=null]
                                                               [n=n2_9064 & 
                                                                 1<=n & 0<=n]
                                                               [0=cl & 
                                                                 0<=cl & 
                                                                 cl<=1]
                                                               [0=cl_9065]
                                                               [!(res)]))&
                                                              {FLOW,(20,21)=__norm})
                                                           )
                           
                           })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_red$node SUCCESS

Checking procedure remove_min$node... 
!!! REL :  RMVM1(n,n1)
!!! POST:  n1>=0 & n1+1=n
!!! PRE :  true
!!! REL :  RMVM2(n,n2)
!!! POST:  n2>=0 & n2+1=n
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMVM1,RMVM2]
              EBase exists (Expl)(Impl)[n; 
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{697,696}]&(
                    ([null!=x][0<=cl & cl<=1][0<=n & 0!=n]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 63::ref [x]
                                
                                EXISTS(cl2,
                                n1: x'::rb2<n1,cl2>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                                (
                                ([1=cl][0<=cl2 & cl2<=1][0<=n1 & RMVM1(n,n1)]
                                 ))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_421_116,
                                   n2: x'::rb2<n2,flted_421_116>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                   (
                                   ([0=flted_421_116][0=cl]
                                    [0<=n2 & RMVM2(n,n2)]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{697,696}]&(
                  ([x!=null][1<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 63::ref [x]
                              
                              EXISTS(cl2_9617,
                              n1_9618: x'::rb2<n1_9618,cl2_9617>@M[Orig][LHSCase]@ rem br[{698,697,696}]&
                              (
                              ([1+n1_9618=n & 0<=n & 0<=n1_9618]
                               [0<=cl2_9617 & cl2_9617<=1]
                               [cl=1 & 0<=cl & cl<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_421_9619,
                                 n2_9620: x'::rb2<n2_9620,flted_421_9619>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                 (
                                 ([1+n2_9620=n & 0<=n & 0<=n2_9620]
                                  [cl=0 & 0<=cl & cl<=1][0=flted_421_9619]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (n2=n-1 & 2<=n) --> RMVM2(n,n2),
 (n1=n-1 & 1<=n) --> RMVM1(n,n1),
 (n2=n-1 & 1<=n) --> RMVM2(n,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_24_471,
                    flted_24_472,
                    flted_24_473: a::rb2<na,flted_24_473>@M[Orig][LHSCase]@ rem br[{697}] * 
                    b::rb2<nb,flted_24_472>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_24_471>@M[Orig][LHSCase]@ rem br[{698,696}]&
                    (
                    ([flted_24_473=1][0=flted_24_472][0=flted_24_471]
                     [null!=a][0<=na & 0!=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(flted_25_470,
                                n: res::rb2<n,flted_25_470>@M[Orig][LHSCase]@ rem br[{696}]&
                                (([flted_25_470=0][null!=res][0<=n & 0!=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_24_473>@M[Orig][LHSCase]@ rem br[{697}] * 
                  b::rb2<nb,flted_24_472>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_24_471>@M[Orig][LHSCase]@ rem br[{698,696}]&
                  (
                  ([a!=null][1<=na][0<=nb][0<=nc][1=flted_24_473]
                   [0=flted_24_472][0=flted_24_471]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(n_9734,
                              flted_25_9735: res::rb2<n_9734,flted_25_9735>@M[Orig][LHSCase]@ rem br[{696}]&
                              (
                              ([2+na+nb+nc=n_9734 & 0<=na & (3+nb+
                                 nc)<=n_9734 & 0<=nb & 0<=nc]
                               [res!=null][a!=null][0=flted_25_9735]
                               [0<=flted_24_471 & flted_24_471<=1]
                               [0<=flted_24_472 & flted_24_472<=1]
                               [0<=flted_24_473 & flted_24_473<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_66_429,
                    flted_66_430,
                    flted_66_431: a::rb2<na,flted_66_431>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    b::rb2<nb,flted_66_430>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                    c::rb2<nc,flted_66_429>@M[Orig][LHSCase]@ rem br[{697}]&(
                    ([0=flted_66_431][0=flted_66_430][flted_66_429=1]
                     [null!=c][0<=na][0<=nb][0<=nc & 0!=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_67_428,
                                n: res::rb2<n,flted_67_428>@M[Orig][LHSCase]@ rem br[{698,696}]&
                                (([0=flted_67_428][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_66_431>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  b::rb2<nb,flted_66_430>@M[Orig][LHSCase]@ rem br[{698,696}] * 
                  c::rb2<nc,flted_66_429>@M[Orig][LHSCase]@ rem br[{697}]&(
                  ([c!=null][0<=na][0<=nb][1<=nc][0=flted_66_431]
                   [0=flted_66_430][1=flted_66_429]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(n_9849,
                              flted_67_9850: res::rb2<n_9849,flted_67_9850>@M[Orig][LHSCase]@ rem br[{698,696}]&
                              (
                              ([2+na+nb+nc=n_9849 & (2+na+nc)<=n_9849 & 
                                 0<=nb & 1<=nc & 0<=nc & 0<=na]
                               [res!=null][c!=null][0=flted_67_9850]
                               [0<=flted_66_429 & flted_66_429<=1]
                               [0<=flted_66_430 & flted_66_430<=1]
                               [0<=flted_66_431 & flted_66_431<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 3237 invocations 
324 false contexts at: ( (494,3)  (494,10)  (491,4)  (491,11)  (486,22)  (486,29)  (485,26)  (485,71)  (485,56)  (485,42)  (485,34)  (485,22)  (485,22)  (480,26)  (480,33)  (479,30)  (479,100)  (479,85)  (479,65)  (479,46)  (479,38)  (479,26)  (479,26)  (475,28)  (475,35)  (474,32)  (474,62)  (474,48)  (474,40)  (474,28)  (474,28)  (470,28)  (470,35)  (469,32)  (469,62)  (469,48)  (469,40)  (469,28)  (469,28)  (467,39)  (467,28)  (467,28)  (467,24)  (466,37)  (466,26)  (466,22)  (464,33)  (464,22)  (464,18)  (460,20)  (460,27)  (457,22)  (457,29)  (456,26)  (456,56)  (456,42)  (456,34)  (456,22)  (456,22)  (454,22)  (454,22)  (454,18)  (452,27)  (452,18)  (452,14)  (450,25)  (450,14)  (450,10)  (448,6)  (448,22)  (448,19)  (118,2)  (118,9)  (123,3)  (123,10)  (121,3)  (121,10)  (120,17)  (120,6)  (120,6)  (120,2)  (144,2)  (144,9)  (149,3)  (149,10)  (147,3)  (147,10)  (146,17)  (146,6)  (146,6)  (146,2)  (738,14)  (735,16)  (731,24)  (728,28)  (728,35)  (727,32)  (727,71)  (727,57)  (727,49)  (727,28)  (727,28)  (723,28)  (723,35)  (722,44)  (722,28)  (721,43)  (721,28)  (721,28)  (719,37)  (719,28)  (719,24)  (714,24)  (714,31)  (713,28)  (713,85)  (713,65)  (713,46)  (713,38)  (713,24)  (713,24)  (709,24)  (709,31)  (708,40)  (708,24)  (707,39)  (707,24)  (707,24)  (705,33)  (705,24)  (705,20)  (692,12)  (689,16)  (685,24)  (681,30)  (681,37)  (680,34)  (680,95)  (680,75)  (680,56)  (680,43)  (680,30)  (680,30)  (676,30)  (676,37)  (675,46)  (675,30)  (674,45)  (674,30)  (674,30)  (672,39)  (672,30)  (672,26)  (665,26)  (665,33)  (664,30)  (664,73)  (664,59)  (664,46)  (664,26)  (664,26)  (660,26)  (660,33)  (659,42)  (659,26)  (658,41)  (658,26)  (658,26)  (656,35)  (656,26)  (656,22)  (596,14)  (617,30)  (617,75)  (617,60)  (617,46)  (617,38)  (617,26)  (615,32)  (615,102)  (615,87)  (615,67)  (615,48)  (615,40)  (615,28)  (612,36)  (612,66)  (612,52)  (612,44)  (612,32)  (610,36)  (610,66)  (610,52)  (610,44)  (610,32)  (609,45)  (609,34)  (609,34)  (609,30)  (607,41)  (607,30)  (607,26)  (606,39)  (606,28)  (606,24)  (602,30)  (602,60)  (602,46)  (602,38)  (602,26)  (601,28)  (601,28)  (601,24)  (599,33)  (599,24)  (599,20)  (598,33)  (598,22)  (598,18)  (596,18)  (596,34)  (596,31)  (569,14)  (588,34)  (588,79)  (588,70)  (588,56)  (588,43)  (588,30)  (586,32)  (586,102)  (586,93)  (586,73)  (586,54)  (586,41)  (586,28)  (584,34)  (584,70)  (584,56)  (584,43)  (584,30)  (582,34)  (582,70)  (582,56)  (582,43)  (582,30)  (581,43)  (581,32)  (581,32)  (581,28)  (580,41)  (580,30)  (580,26)  (579,39)  (579,28)  (579,24)  (575,30)  (575,64)  (575,50)  (575,37)  (575,26)  (574,28)  (574,28)  (574,24)  (572,33)  (572,24)  (572,20)  (571,33)  (571,22)  (571,18)  (569,18)  (569,35)  (569,32)  (536,14)  (556,32)  (556,77)  (556,68)  (556,54)  (556,41)  (556,28)  (554,34)  (554,104)  (554,95)  (554,75)  (554,56)  (554,43)  (554,30)  (552,36)  (552,72)  (552,58)  (552,45)  (552,32)  (550,36)  (550,72)  (550,58)  (550,45)  (550,32)  (549,45)  (549,34)  (549,34)  (549,30)  (548,43)  (548,32)  (548,28)  (547,41)  (547,30)  (547,26)  (543,32)  (543,68)  (543,54)  (543,41)  (543,28)  (542,30)  (542,30)  (542,26)  (540,35)  (540,26)  (540,22)  (538,33)  (538,22)  (538,18)  (536,18)  (536,35)  (536,32) )

Total verification time: 2.76 second(s)
	Time spent in main process: 2.05 second(s)
	Time spent in child processes: 0.71 second(s)
