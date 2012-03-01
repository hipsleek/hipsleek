
Processing file "rb_ms.ss"
Parsing rb_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure case_2$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d,res]
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)EXISTS(flted_45_455,flted_45_456,flted_45_457,
                    flted_45_458: a::rb2<na,flted_45_458>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_45_457>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_45_456>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    d::rb2<nd,flted_45_455>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([0=flted_45_458][0=flted_45_457][0=flted_45_456]
                     [0=flted_45_455][0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(flted_46_454,
                                n: res::rb2<n,flted_46_454>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_46_454][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)a::rb2<na,flted_45_458>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_45_457>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_45_456>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  d::rb2<nd,flted_45_455>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_45_458]
                   [0=flted_45_457][0=flted_45_456][0=flted_45_455]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(n_3619,
                              flted_46_3620: res::rb2<n_3619,flted_46_3620>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([3+na+nb+nc+nd=n_3619 & (3+na+nc+
                                 nd)<=n_3619 & 0<=nb & 0<=na & 0<=nd & 0<=nc]
                               [res!=null][0=flted_46_3620]
                               [0<=flted_45_455 & flted_45_455<=1]
                               [0<=flted_45_456 & flted_45_456<=1]
                               [0<=flted_45_457 & flted_45_457<=1]
                               [0<=flted_45_458 & flted_45_458<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)EXISTS(flted_87_413,flted_87_414,flted_87_415,
                    flted_87_416: a::rb2<na,flted_87_416>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_87_415>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_87_414>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    d::rb2<nd,flted_87_413>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([0=flted_87_416][0=flted_87_415][0=flted_87_414]
                     [0=flted_87_413][0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(flted_88_412,
                                n: res::rb2<n,flted_88_412>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_88_412][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)a::rb2<na,flted_87_416>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_87_415>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_87_414>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  d::rb2<nd,flted_87_413>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_87_416]
                   [0=flted_87_415][0=flted_87_414][0=flted_87_413]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(n_3715,
                              flted_88_3716: res::rb2<n_3715,flted_88_3716>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([res!=null]
                               [3+na+nb+nc+nd=n_3715 & (3+na+nb+
                                 nc)<=n_3715 & 0<=nc & 0<=nb & 0<=nd & 0<=na]
                               [0=flted_88_3716]
                               [0<=flted_87_413 & flted_87_413<=1]
                               [0<=flted_87_414 & flted_87_414<=1]
                               [0<=flted_87_415 & flted_87_415<=1]
                               [0<=flted_87_416 & flted_87_416<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure del_2r$node~node~node... 
assert/assume:rb_ms.ss:391: 1:  : failed


assert:rb_ms.ss:392: 1:  : ok


Procedure del_2r$node~node~node SUCCESS

Checking procedure del$node~int... 
assert/assume:rb_ms.ss:520: 4:  : failed


assert/assume:rb_ms.ss:521: 7:  : failed


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
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                    (([0<=cl & cl<=1][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 78::ref [x]
                                
                                EXISTS(cl2,
                                n1: x'::rb2<n1,cl2>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                (
                                ([1=cl][0<=cl2 & cl2<=1][0<=n1 & DEL1(n,n1)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_504_112,
                                   n2: x'::rb2<n2,flted_504_112>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                   (
                                   ([0=flted_504_112][0=cl]
                                    [0<=n2 & DEL2(n,n2)]))&
                                   {FLOW,(20,21)=__norm})
                                or EXISTS(cl_113,
                                   n3: x'::rb2<n3,cl_113>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                   (
                                   ([0<=n3 & DEL3(n,n3)]
                                    [cl=cl_113 & cl_113<=1 & 0<=cl_113]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                  (([0<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 78::ref [x]
                              
                              EXISTS(flted_504_5468,
                              n2_5469: x'::rb2<n2_5469,flted_504_5468>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([n2_5469<=n & 0<=n & 0<=n2_5469 & (-1+
                                 n)<=n2_5469]
                               [cl=0 & 0<=cl & cl<=1][0=flted_504_5468]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl2_5470,
                                 n1_5471: x'::rb2<n1_5471,cl2_5470>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                 (
                                 ([1+n1_5471=n & 0<=n & 0<=n1_5471]
                                  [0<=cl2_5470 & cl2_5470<=1]
                                  [cl=1 & 0<=cl & cl<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(cl_5472,
                                 n3_5473: x'::rb2<n3_5473,cl_5472>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                 (
                                 ([n3_5473<=n & 0<=n & 0<=n3_5473 & (-1+
                                    n)<=n3_5473]
                                  [cl=cl_5472 & cl<=1 & 0<=cl]))&
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
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_301_194,
                    flted_301_195,
                    flted_301_196: a::rb2<na,flted_301_196>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_301_195>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_301_194>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([0=flted_301_196][0=flted_301_195][0=flted_301_194]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(flted_302_193,
                                n: res::rb2<n,flted_302_193>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_302_193][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_301_196>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_301_195>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_301_194>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_301_196][0=flted_301_195]
                   [0=flted_301_194]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(n_6057,
                              flted_302_6058: res::rb2<n_6057,flted_302_6058>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([2+na+nb+nc=n_6057 & 0<=na & (2+nb+
                                 nc)<=n_6057 & 0<=nb & 0<=nc]
                               [res!=null][0=flted_302_6058]
                               [0<=flted_301_194 & flted_301_194<=1]
                               [0<=flted_301_195 & flted_301_195<=1]
                               [0<=flted_301_196 & flted_301_196<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_321_175,
                    flted_321_176,
                    flted_321_177: a::rb2<na,flted_321_177>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_321_176>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_321_175>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([0=flted_321_177][0=flted_321_176][0=flted_321_175]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(flted_322_174,
                                n: res::rb2<n,flted_322_174>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_322_174][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_321_177>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_321_176>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_321_175>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_321_177][0=flted_321_176]
                   [0=flted_321_175]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(n_6172,
                              flted_322_6173: res::rb2<n_6172,flted_322_6173>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([2+na+nb+nc=n_6172 & (2+na+nc)<=n_6172 & 
                                 0<=nb & 0<=nc & 0<=na]
                               [res!=null][0=flted_322_6173]
                               [0<=flted_321_175 & flted_321_175<=1]
                               [0<=flted_321_176 & flted_321_176<=1]
                               [0<=flted_321_177 & flted_321_177<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_262_232,
                    flted_262_233,
                    flted_262_234: a::rb2<na,flted_262_234>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_262_233>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_262_232>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([0=flted_262_234][0=flted_262_233][0=flted_262_232]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_263_231,
                                n: res::rb2<n,flted_263_231>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_263_231][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_262_234>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_262_233>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_262_232>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_262_234][0=flted_262_233]
                   [0=flted_262_232]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(n_6295,
                              flted_263_6296: res::rb2<n_6295,flted_263_6296>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([2+na+nb+nc=n_6295 & (2+na+nc)<=n_6295 & 
                                 0<=nb & 0<=na & 0<=nc]
                               [res!=null][0=flted_263_6296]
                               [0<=flted_262_232 & flted_262_232<=1]
                               [0<=flted_262_233 & flted_262_233<=1]
                               [0<=flted_262_234 & flted_262_234<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_281_213,
                    flted_281_214,
                    flted_281_215: a::rb2<na,flted_281_215>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_281_214>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_281_213>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([0=flted_281_215][0=flted_281_214][0=flted_281_213]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                EXISTS(flted_282_212,
                                n: res::rb2<n,flted_282_212>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_282_212][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_281_215>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_281_214>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_281_213>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_281_215][0=flted_281_214]
                   [0=flted_281_213]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              EXISTS(n_6410,
                              flted_282_6411: res::rb2<n_6410,flted_282_6411>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([2+na+nb+nc=n_6410 & (2+na+nc)<=n_6410 & 
                                 0<=nb & 0<=nc & 0<=na]
                               [res!=null][0=flted_282_6411]
                               [0<=flted_281_213 & flted_281_213<=1]
                               [0<=flted_281_214 & flted_281_214<=1]
                               [0<=flted_281_215 & flted_281_215<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d,res]
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)
                           EXISTS(flted_215_304,flted_215_305,flted_215_306,
                           flted_215_307: a::rb2<na,flted_215_307>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           b::rb2<nb,flted_215_306>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           c::rb2<nc,flted_215_305>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           d::rb2<nd,flted_215_304>@M[Orig][LHSCase]@ rem br[{706,704}]&
                           (
                           ([0=flted_215_307][0=flted_215_306]
                            [0=flted_215_305][0=flted_215_304][0=color]
                            [0<=na][0<=nb][0<=nc][0<=nd]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_216_308,flted_216_309,
                              flted_216_310,
                              flted_216_311: a::rb2<na,flted_216_311>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              b::rb2<nb,flted_216_310>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              c::rb2<nc,flted_216_309>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              d::rb2<nd,flted_216_308>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([0=flted_216_311][0=flted_216_310]
                               [0=flted_216_309][0=flted_216_308][1=color]
                               [0<=na][0<=nb][0<=nc][0<=nd]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 32::
                                
                                EXISTS(flted_217_302,
                                n1: res::rb2<n1,flted_217_302>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_217_302][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_218_303,
                                   n2: res::rb2<n2,flted_218_303>@M[Orig][LHSCase]@ rem br[{705}]&
                                   (
                                   ([flted_218_303=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)
                         a::rb2<na,flted_215_307>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         b::rb2<nb,flted_215_306>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         c::rb2<nc,flted_215_305>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         d::rb2<nd,flted_215_304>@M[Orig][LHSCase]@ rem br[{706,704}]&
                         (
                         ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_215_307]
                          [0=flted_215_306][0=flted_215_305][0=flted_215_304]
                          [0=color]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_216_311>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            b::rb2<nb,flted_216_310>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            c::rb2<nc,flted_216_309>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            d::rb2<nd,flted_216_308>@M[Orig][LHSCase]@ rem br[{706,704}]&
                            (
                            ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_216_311]
                             [0=flted_216_310][0=flted_216_309]
                             [0=flted_216_308][1=color]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 32::
                              
                              EXISTS(n1_6707,
                              flted_217_6708: res::rb2<n1_6707,flted_217_6708>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([(0<=flted_215_307 & flted_215_307<=1 & 
                                 0<=na & 0<=flted_215_306 & 
                                 flted_215_306<=1 & 0<=nb & 
                                 0<=flted_215_305 & flted_215_305<=1 & 
                                 0<=nc & 0<=flted_215_304 & 
                                 flted_215_304<=1 & 0<=nd | 
                                 0<=flted_216_311 & flted_216_311<=1 & 
                                 0<=na & 0<=flted_216_310 & 
                                 flted_216_310<=1 & 0<=nb & 
                                 0<=flted_216_309 & flted_216_309<=1 & 
                                 0<=nc & 0<=flted_216_308 & 
                                 flted_216_308<=1 & 0<=nd) & n1_6707=3+na+nb+
                                 nc+nd & 0<=nd & 0<=na & 0<=nb & 0<=nc]
                               [res!=null][0=flted_217_6708][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_6709,
                                 flted_218_6710: res::rb2<n2_6709,flted_218_6710>@M[Orig][LHSCase]@ rem br[{705}]&
                                 (
                                 ([(0<=flted_215_307 & flted_215_307<=1 & 
                                    0<=na & 0<=flted_215_306 & 
                                    flted_215_306<=1 & 0<=nb & 
                                    0<=flted_215_305 & flted_215_305<=1 & 
                                    0<=nc & 0<=flted_215_304 & 
                                    flted_215_304<=1 & 0<=nd | 
                                    0<=flted_216_311 & flted_216_311<=1 & 
                                    0<=na & 0<=flted_216_310 & 
                                    flted_216_310<=1 & 0<=nb & 
                                    0<=flted_216_309 & flted_216_309<=1 & 
                                    0<=nc & 0<=flted_216_308 & 
                                    flted_216_308<=1 & 0<=nd) & n2_6709=3+na+
                                    nb+nc+nd & 0<=nb & 0<=na & 0<=nd & 0<=nc]
                                  [res!=null][1=flted_218_6710][1=color]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5$node~node~node~node~int SUCCESS

Checking procedure del_5r$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d,res]
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)
                           EXISTS(flted_240_259,flted_240_260,flted_240_261,
                           flted_240_262: a::rb2<na,flted_240_262>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           b::rb2<nb,flted_240_261>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           c::rb2<nc,flted_240_260>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           d::rb2<nd,flted_240_259>@M[Orig][LHSCase]@ rem br[{706,704}]&
                           (
                           ([0=flted_240_262][0=flted_240_261]
                            [0=flted_240_260][0=flted_240_259][0=color]
                            [0<=na][0<=nb][0<=nc][0<=nd]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_241_263,flted_241_264,
                              flted_241_265,
                              flted_241_266: a::rb2<na,flted_241_266>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              b::rb2<nb,flted_241_265>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              c::rb2<nc,flted_241_264>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              d::rb2<nd,flted_241_263>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([0=flted_241_266][0=flted_241_265]
                               [0=flted_241_264][0=flted_241_263][1=color]
                               [0<=na][0<=nb][0<=nc][0<=nd]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                
                                EXISTS(flted_242_257,
                                n1: res::rb2<n1,flted_242_257>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_242_257][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_243_258,
                                   n2: res::rb2<n2,flted_243_258>@M[Orig][LHSCase]@ rem br[{705}]&
                                   (
                                   ([flted_243_258=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)
                         a::rb2<na,flted_240_262>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         b::rb2<nb,flted_240_261>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         c::rb2<nc,flted_240_260>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         d::rb2<nd,flted_240_259>@M[Orig][LHSCase]@ rem br[{706,704}]&
                         (
                         ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_240_262]
                          [0=flted_240_261][0=flted_240_260][0=flted_240_259]
                          [0=color]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_241_266>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            b::rb2<nb,flted_241_265>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            c::rb2<nc,flted_241_264>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            d::rb2<nd,flted_241_263>@M[Orig][LHSCase]@ rem br[{706,704}]&
                            (
                            ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_241_266]
                             [0=flted_241_265][0=flted_241_264]
                             [0=flted_241_263][1=color]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              
                              EXISTS(n1_7014,
                              flted_242_7015: res::rb2<n1_7014,flted_242_7015>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([(0<=flted_240_262 & flted_240_262<=1 & 
                                 0<=na & 0<=flted_240_261 & 
                                 flted_240_261<=1 & 0<=nb & 
                                 0<=flted_240_260 & flted_240_260<=1 & 
                                 0<=nc & 0<=flted_240_259 & 
                                 flted_240_259<=1 & 0<=nd | 
                                 0<=flted_241_266 & flted_241_266<=1 & 
                                 0<=na & 0<=flted_241_265 & 
                                 flted_241_265<=1 & 0<=nb & 
                                 0<=flted_241_264 & flted_241_264<=1 & 
                                 0<=nc & 0<=flted_241_263 & 
                                 flted_241_263<=1 & 0<=nd) & n1_7014=3+na+nb+
                                 nc+nd & 0<=na & 0<=nc & 0<=nb & 0<=nd]
                               [res!=null][0=flted_242_7015][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_7016,
                                 flted_243_7017: res::rb2<n2_7016,flted_243_7017>@M[Orig][LHSCase]@ rem br[{705}]&
                                 (
                                 ([res!=null]
                                  [(0<=flted_240_262 & flted_240_262<=1 & 
                                    0<=na & 0<=flted_240_261 & 
                                    flted_240_261<=1 & 0<=nb & 
                                    0<=flted_240_260 & flted_240_260<=1 & 
                                    0<=nc & 0<=flted_240_259 & 
                                    flted_240_259<=1 & 0<=nd | 
                                    0<=flted_241_266 & flted_241_266<=1 & 
                                    0<=na & 0<=flted_241_265 & 
                                    flted_241_265<=1 & 0<=nb & 
                                    0<=flted_241_264 & flted_241_264<=1 & 
                                    0<=nc & 0<=flted_241_263 & 
                                    flted_241_263<=1 & 0<=nd) & n2_7016=3+na+
                                    nb+nc+nd & 0<=na & 0<=nb & 0<=nc & 0<=nd]
                                  [1=flted_243_7017][1=color]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5r$node~node~node~node~int SUCCESS

Checking procedure del_6$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer [res,c,a,b]
              EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; 
                    nc](ex)
                           EXISTS(flted_161_374,
                           flted_161_375: a::rb2<na,flted_161_375>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                           b::rb2<nb,Anon_15>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                           c::rb2<nc,flted_161_374>@M[Orig][LHSCase]@ rem br[{705}]&
                           (
                           ([0=flted_161_375][flted_161_374=1][0=color]
                            [null!=c][0<=na][0<=nb][Anon_15<=1 & 0<=Anon_15]
                            [0<=nc & 0!=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_162_376,
                              flted_162_377: a::rb2<na,flted_162_377>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                              b::rb2<nb,Anon_16>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                              c::rb2<nc,flted_162_376>@M[Orig][LHSCase]@ rem br[{705}]&
                              (
                              ([0=flted_162_377][flted_162_376=1][1=color]
                               [null!=c][0<=na][0<=nb]
                               [Anon_16<=1 & 0<=Anon_16][0<=nc & 0!=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 24::
                                
                                EXISTS(flted_163_372,
                                n1: res::rb2<n1,flted_163_372>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_163_372][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_164_373,
                                   n2: res::rb2<n2,flted_164_373>@M[Orig][LHSCase]@ rem br[{705}]&
                                   (
                                   ([flted_164_373=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; 
                  nc](ex)
                         a::rb2<na,flted_161_375>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                         b::rb2<nb,Anon_15>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                         c::rb2<nc,flted_161_374>@M[Orig][LHSCase]@ rem br[{705}]&
                         (
                         ([c!=null][0<=na][0<=nb][1<=nc][0=flted_161_375]
                          [1=flted_161_374][0=color][Anon_15<=1 & 0<=Anon_15]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_162_377>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                            b::rb2<nb,Anon_16>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                            c::rb2<nc,flted_162_376>@M[Orig][LHSCase]@ rem br[{705}]&
                            (
                            ([c!=null][0<=na][0<=nb][1<=nc][0=flted_162_377]
                             [1=flted_162_376][1=color]
                             [Anon_16<=1 & 0<=Anon_16]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 24::
                              
                              EXISTS(n1_7536,
                              flted_163_7537: res::rb2<n1_7536,flted_163_7537>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_161_375 & flted_161_375<=1 & 
                                 0<=na & 0<=Anon_15 & Anon_15<=1 & 0<=nb & 
                                 0<=flted_161_374 & flted_161_374<=1 & 
                                 0<=nc | 0<=flted_162_377 & 
                                 flted_162_377<=1 & 0<=na & 0<=Anon_16 & 
                                 Anon_16<=1 & 0<=nb & 0<=flted_162_376 & 
                                 flted_162_376<=1 & 0<=nc) & 2+na+nb+
                                 nc=n1_7536 & 1<=nc & (2+nb+nc)<=n1_7536 & 
                                 0<=nb]
                               [res!=null][c!=null][0=color]
                               [0=flted_163_7537]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_7538,
                                 flted_164_7539: res::rb2<n2_7538,flted_164_7539>@M[Orig][LHSCase]@ rem br[{705}]&
                                 (
                                 ([Anon_16<=1 & 0<=Anon_16 & 
                                    (0<=flted_161_375 & flted_161_375<=1 & 
                                    0<=na & 0<=Anon_15 & Anon_15<=1 & 
                                    0<=nb & 0<=flted_161_374 & 
                                    flted_161_374<=1 & 0<=nc | 
                                    0<=flted_162_377 & flted_162_377<=1 & 
                                    0<=na & 0<=Anon_16 & Anon_16<=1 & 
                                    0<=nb & 0<=flted_162_376 & 
                                    flted_162_376<=1 & 0<=nc) & 2+na+nb+
                                    nc=n2_7538 & 1<=nc & (2+nb+
                                    nc)<=n2_7538 & 0<=nb]
                                  [res!=null][c!=null][1=color]
                                  [1=flted_164_7539]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6$node~node~node~int SUCCESS

Checking procedure del_6r$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,res]
              EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; 
                    nc](ex)
                           EXISTS(flted_188_345,
                           flted_188_346: a::rb2<na,flted_188_346>@M[Orig][LHSCase]@ rem br[{705}] * 
                           b::rb2<nb,Anon_19>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                           c::rb2<nc,flted_188_345>@M[Orig][LHSCase]@ rem br[{706,704}]&
                           (
                           ([flted_188_346=1][0=flted_188_345][0=color]
                            [null!=a][0<=na & 0!=na][0<=nb]
                            [Anon_19<=1 & 0<=Anon_19][0<=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_189_347,
                              flted_189_348: a::rb2<na,flted_189_348>@M[Orig][LHSCase]@ rem br[{705}] * 
                              b::rb2<nb,Anon_20>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                              c::rb2<nc,flted_189_347>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([flted_189_348=1][0=flted_189_347][1=color]
                               [null!=a][0<=na & 0!=na][0<=nb]
                               [Anon_20<=1 & 0<=Anon_20][0<=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                
                                EXISTS(flted_190_343,
                                n1: res::rb2<n1,flted_190_343>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_190_343][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_191_344,
                                   n2: res::rb2<n2,flted_191_344>@M[Orig][LHSCase]@ rem br[{705}]&
                                   (
                                   ([flted_191_344=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; 
                  nc](ex)
                         a::rb2<na,flted_188_346>@M[Orig][LHSCase]@ rem br[{705}] * 
                         b::rb2<nb,Anon_19>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                         c::rb2<nc,flted_188_345>@M[Orig][LHSCase]@ rem br[{706,704}]&
                         (
                         ([a!=null][1<=na][0<=nb][0<=nc][1=flted_188_346]
                          [0=flted_188_345][0=color][Anon_19<=1 & 0<=Anon_19]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_189_348>@M[Orig][LHSCase]@ rem br[{705}] * 
                            b::rb2<nb,Anon_20>@M[Orig][LHSCase]@ rem br[{706,705,704}] * 
                            c::rb2<nc,flted_189_347>@M[Orig][LHSCase]@ rem br[{706,704}]&
                            (
                            ([a!=null][1<=na][0<=nb][0<=nc][1=flted_189_348]
                             [0=flted_189_347][1=color]
                             [Anon_20<=1 & 0<=Anon_20]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              
                              EXISTS(n1_8074,
                              flted_190_8075: res::rb2<n1_8074,flted_190_8075>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_188_346 & flted_188_346<=1 & 
                                 0<=na & 0<=Anon_19 & Anon_19<=1 & 0<=nb & 
                                 0<=flted_188_345 & flted_188_345<=1 & 
                                 0<=nc | 0<=flted_189_348 & 
                                 flted_189_348<=1 & 0<=na & 0<=Anon_20 & 
                                 Anon_20<=1 & 0<=nb & 0<=flted_189_347 & 
                                 flted_189_347<=1 & 0<=nc) & 2+na+nb+
                                 nc=n1_8074 & 1<=na & (2+na+nb)<=n1_8074 & 
                                 0<=nb]
                               [res!=null][a!=null][0=color]
                               [0=flted_190_8075]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_8076,
                                 flted_191_8077: res::rb2<n2_8076,flted_191_8077>@M[Orig][LHSCase]@ rem br[{705}]&
                                 (
                                 ([Anon_20<=1 & 0<=Anon_20 & 
                                    (0<=flted_188_346 & flted_188_346<=1 & 
                                    0<=na & 0<=Anon_19 & Anon_19<=1 & 
                                    0<=nb & 0<=flted_188_345 & 
                                    flted_188_345<=1 & 0<=nc | 
                                    0<=flted_189_348 & flted_189_348<=1 & 
                                    0<=na & 0<=Anon_20 & Anon_20<=1 & 
                                    0<=nb & 0<=flted_189_347 & 
                                    flted_189_347<=1 & 0<=nc) & 2+na+nb+
                                    nc=n2_8076 & 1<=na & (2+na+
                                    nb)<=n2_8076 & 0<=nb]
                                  [res!=null][a!=null][1=color]
                                  [1=flted_191_8077]))&
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
                    Anon_21](ex)x::rb2<n,Anon_21>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                    (([0<=n][Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 113::
                                EXISTS(Anon_22,
                                n1: res::rb2<n1,Anon_22>@M[Orig][LHSCase]@ rem br[{705,704}]&
                                (
                                ([null!=res][0!=n1 & 0<=n1 & INS(n,n1)]
                                 [Anon_22<=1 & 0<=Anon_22]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  Anon_21](ex)x::rb2<n,Anon_21>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                  (([0<=n][Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 113::
                              EXISTS(Anon_8772,
                              n1_8773: res::rb2<n1_8773,Anon_8772>@M[Orig][LHSCase]@ rem br[{705,704}]&
                              (
                              ([1=n1_8773 & 0!=n1_8773 & 0<=n1_8773]
                               [n=0 & 0<=n][null!=res]
                               [0<=Anon_8772 & Anon_8772<=1]
                               [Anon_21<=1 & 0<=Anon_21]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & n1=1) --> INS(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure is_black$node... 
!!! OLD SPECS: ((None,[]),EInfer [n1,n2]
              ECase case {
                     x=null -> ((None,[]),EBase true&MayLoop&
                                                {FLOW,(1,23)=__flow}
                                                  EAssume 19::
                                                    true&(([res]))&
                                                    {FLOW,(20,21)=__norm})
                     ;
                     x!=null -> ((None,[]),EBase exists (Expl)(Impl)[n; 
                                                 cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                                 (([0<=n][cl<=1 & 0<=cl]))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 20::
                                                             
                                                             EXISTS(cl_395: 
                                                             x::rb2<n1,cl_395>@M[Orig][LHSCase]@ rem br[{705}]&
                                                             (
                                                             ([!(res)]
                                                              [cl=cl_395 & 
                                                                cl=1]
                                                              [0<=n1 & 0!=n1]
                                                              [null!=x]))&
                                                             {FLOW,(20,21)=__norm})
                                                             or EXISTS(cl_396: 
                                                                x::rb2<n2,cl_396>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                                                (
                                                                ([res]
                                                                 [cl=cl_396 & 
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
                                               cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                               (([0<=n][0<=cl & cl<=1]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 20::
                                                           
                                                           EXISTS(n1_8970,
                                                           cl_8971: x::rb2<n1_8970,cl_8971>@M[Orig][LHSCase]@ rem br[{705}]&
                                                           (
                                                           ([n=n1_8970 & 
                                                              1<=n1_8970 & 
                                                              0<=n]
                                                            [x!=null]
                                                            [1=cl & 0<=cl & 
                                                              cl<=1]
                                                            [1=cl_8971]
                                                            [!(res)]))&
                                                           {FLOW,(20,21)=__norm})
                                                           or EXISTS(n2_8972,
                                                              cl_8973: 
                                                              x::rb2<n2_8972,cl_8973>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                                              (
                                                              ([n=n2_8972 & 
                                                                 1<=n & 0<=n]
                                                               [x!=null]
                                                               [0=cl & 
                                                                 0<=cl & 
                                                                 cl<=1]
                                                               [0=cl_8973]
                                                               [res]))&
                                                              {FLOW,(20,21)=__norm})
                                                           )
                   
                   })
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
!!! OLD SPECS: ((None,[]),EInfer [n1,n2]
              EBase exists (Expl)(Impl)[n; 
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
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
                                                             
                                                             EXISTS(cl_401: 
                                                             x::rb2<n1,cl_401>@M[Orig][LHSCase]@ rem br[{705}]&
                                                             (
                                                             ([res]
                                                              [cl=cl_401 & 
                                                                cl=1]
                                                              [0<=n1 & 0!=n1]
                                                              [null!=x]))&
                                                             {FLOW,(20,21)=__norm})
                                                             or EXISTS(cl_402: 
                                                                x::rb2<n2,cl_402>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                                                (
                                                                ([!(res)]
                                                                 [cl=cl_402 & 
                                                                   cl=0]
                                                                 [0<=n2]))&
                                                                {FLOW,(20,21)=__norm})
                                                             )
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
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
                                                           
                                                           EXISTS(n1_9170,
                                                           cl_9171: x::rb2<n1_9170,cl_9171>@M[Orig][LHSCase]@ rem br[{705}]&
                                                           (
                                                           ([n=n1_9170 & 
                                                              1<=n1_9170 & 
                                                              0<=n]
                                                            [x!=null]
                                                            [1=cl & 0<=cl & 
                                                              cl<=1]
                                                            [1=cl_9171][
                                                            res]))&
                                                           {FLOW,(20,21)=__norm})
                                                           or EXISTS(n2_9172,
                                                              cl_9173: 
                                                              x::rb2<n2_9172,cl_9173>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                                              (
                                                              ([x!=null]
                                                               [n=n2_9172 & 
                                                                 1<=n & 0<=n]
                                                               [0=cl & 
                                                                 0<=cl & 
                                                                 cl<=1]
                                                               [0=cl_9173]
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
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{705,704}]&(
                    ([null!=x][0<=cl & cl<=1][0<=n & 0!=n]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 65::ref [x]
                                
                                EXISTS(cl2,
                                n1: x'::rb2<n1,cl2>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                                (
                                ([1=cl][0<=cl2 & cl2<=1][0<=n1 & RMVM1(n,n1)]
                                 ))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_419_116,
                                   n2: x'::rb2<n2,flted_419_116>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                   (
                                   ([0=flted_419_116][0=cl]
                                    [0<=n2 & RMVM2(n,n2)]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{705,704}]&(
                  ([x!=null][1<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 65::ref [x]
                              
                              EXISTS(cl2_9725,
                              n1_9726: x'::rb2<n1_9726,cl2_9725>@M[Orig][LHSCase]@ rem br[{706,705,704}]&
                              (
                              ([1+n1_9726=n & 0<=n & 0<=n1_9726]
                               [0<=cl2_9725 & cl2_9725<=1]
                               [cl=1 & 0<=cl & cl<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_419_9727,
                                 n2_9728: x'::rb2<n2_9728,flted_419_9727>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                 (
                                 ([1+n2_9728=n & 0<=n & 0<=n2_9728]
                                  [cl=0 & 0<=cl & cl<=1][0=flted_419_9727]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (n2=n-1 & 2<=n) --> RMVM2(n,n2),
 (n1=n-1 & 1<=n) --> RMVM1(n,n1),
 (n2=n-1 & 1<=n) --> RMVM2(n,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_24_477,
                    flted_24_478,
                    flted_24_479: a::rb2<na,flted_24_479>@M[Orig][LHSCase]@ rem br[{705}] * 
                    b::rb2<nb,flted_24_478>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_24_477>@M[Orig][LHSCase]@ rem br[{706,704}]&
                    (
                    ([flted_24_479=1][0=flted_24_478][0=flted_24_477]
                     [null!=a][0<=na & 0!=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(flted_25_476,
                                n: res::rb2<n,flted_25_476>@M[Orig][LHSCase]@ rem br[{704}]&
                                (([flted_25_476=0][null!=res][0<=n & 0!=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_24_479>@M[Orig][LHSCase]@ rem br[{705}] * 
                  b::rb2<nb,flted_24_478>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_24_477>@M[Orig][LHSCase]@ rem br[{706,704}]&
                  (
                  ([a!=null][1<=na][0<=nb][0<=nc][1=flted_24_479]
                   [0=flted_24_478][0=flted_24_477]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(n_9842,
                              flted_25_9843: res::rb2<n_9842,flted_25_9843>@M[Orig][LHSCase]@ rem br[{704}]&
                              (
                              ([2+na+nb+nc=n_9842 & 0<=na & (3+nb+
                                 nc)<=n_9842 & 0<=nb & 0<=nc]
                               [res!=null][a!=null][0=flted_25_9843]
                               [0<=flted_24_477 & flted_24_477<=1]
                               [0<=flted_24_478 & flted_24_478<=1]
                               [0<=flted_24_479 & flted_24_479<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_66_435,
                    flted_66_436,
                    flted_66_437: a::rb2<na,flted_66_437>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    b::rb2<nb,flted_66_436>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                    c::rb2<nc,flted_66_435>@M[Orig][LHSCase]@ rem br[{705}]&(
                    ([0=flted_66_437][0=flted_66_436][flted_66_435=1]
                     [null!=c][0<=na][0<=nb][0<=nc & 0!=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_67_434,
                                n: res::rb2<n,flted_67_434>@M[Orig][LHSCase]@ rem br[{706,704}]&
                                (([0=flted_67_434][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_66_437>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  b::rb2<nb,flted_66_436>@M[Orig][LHSCase]@ rem br[{706,704}] * 
                  c::rb2<nc,flted_66_435>@M[Orig][LHSCase]@ rem br[{705}]&(
                  ([c!=null][0<=na][0<=nb][1<=nc][0=flted_66_437]
                   [0=flted_66_436][1=flted_66_435]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(n_9957,
                              flted_67_9958: res::rb2<n_9957,flted_67_9958>@M[Orig][LHSCase]@ rem br[{706,704}]&
                              (
                              ([2+na+nb+nc=n_9957 & (2+na+nc)<=n_9957 & 
                                 0<=nb & 1<=nc & 0<=nc & 0<=na]
                               [res!=null][c!=null][0=flted_67_9958]
                               [0<=flted_66_435 & flted_66_435<=1]
                               [0<=flted_66_436 & flted_66_436<=1]
                               [0<=flted_66_437 & flted_66_437<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 3621 invocations 
324 false contexts at: ( (492,3)  (492,10)  (489,4)  (489,11)  (484,22)  (484,29)  (483,26)  (483,71)  (483,56)  (483,42)  (483,34)  (483,22)  (483,22)  (478,26)  (478,33)  (477,30)  (477,100)  (477,85)  (477,65)  (477,46)  (477,38)  (477,26)  (477,26)  (473,28)  (473,35)  (472,32)  (472,62)  (472,48)  (472,40)  (472,28)  (472,28)  (468,28)  (468,35)  (467,32)  (467,62)  (467,48)  (467,40)  (467,28)  (467,28)  (465,39)  (465,28)  (465,28)  (465,24)  (464,37)  (464,26)  (464,22)  (462,33)  (462,22)  (462,18)  (458,20)  (458,27)  (455,22)  (455,29)  (454,26)  (454,56)  (454,42)  (454,34)  (454,22)  (454,22)  (452,22)  (452,22)  (452,18)  (450,27)  (450,18)  (450,14)  (448,25)  (448,14)  (448,10)  (446,6)  (446,22)  (446,19)  (118,2)  (118,9)  (123,3)  (123,10)  (121,3)  (121,10)  (120,17)  (120,6)  (120,6)  (120,2)  (144,2)  (144,9)  (149,3)  (149,10)  (147,3)  (147,10)  (146,17)  (146,6)  (146,6)  (146,2)  (735,14)  (732,16)  (728,24)  (725,28)  (725,35)  (724,32)  (724,71)  (724,57)  (724,49)  (724,28)  (724,28)  (720,28)  (720,35)  (719,44)  (719,28)  (718,43)  (718,28)  (718,28)  (716,37)  (716,28)  (716,24)  (711,24)  (711,31)  (710,28)  (710,85)  (710,65)  (710,46)  (710,38)  (710,24)  (710,24)  (706,24)  (706,31)  (705,40)  (705,24)  (704,39)  (704,24)  (704,24)  (702,33)  (702,24)  (702,20)  (689,12)  (686,16)  (682,24)  (678,30)  (678,37)  (677,34)  (677,95)  (677,75)  (677,56)  (677,43)  (677,30)  (677,30)  (673,30)  (673,37)  (672,46)  (672,30)  (671,45)  (671,30)  (671,30)  (669,39)  (669,30)  (669,26)  (662,26)  (662,33)  (661,30)  (661,73)  (661,59)  (661,46)  (661,26)  (661,26)  (657,26)  (657,33)  (656,42)  (656,26)  (655,41)  (655,26)  (655,26)  (653,35)  (653,26)  (653,22)  (593,14)  (614,30)  (614,75)  (614,60)  (614,46)  (614,38)  (614,26)  (612,32)  (612,102)  (612,87)  (612,67)  (612,48)  (612,40)  (612,28)  (609,36)  (609,66)  (609,52)  (609,44)  (609,32)  (607,36)  (607,66)  (607,52)  (607,44)  (607,32)  (606,45)  (606,34)  (606,34)  (606,30)  (604,41)  (604,30)  (604,26)  (603,39)  (603,28)  (603,24)  (599,30)  (599,60)  (599,46)  (599,38)  (599,26)  (598,28)  (598,28)  (598,24)  (596,33)  (596,24)  (596,20)  (595,33)  (595,22)  (595,18)  (593,18)  (593,34)  (593,31)  (566,14)  (585,34)  (585,79)  (585,70)  (585,56)  (585,43)  (585,30)  (583,32)  (583,102)  (583,93)  (583,73)  (583,54)  (583,41)  (583,28)  (581,34)  (581,70)  (581,56)  (581,43)  (581,30)  (579,34)  (579,70)  (579,56)  (579,43)  (579,30)  (578,43)  (578,32)  (578,32)  (578,28)  (577,41)  (577,30)  (577,26)  (576,39)  (576,28)  (576,24)  (572,30)  (572,64)  (572,50)  (572,37)  (572,26)  (571,28)  (571,28)  (571,24)  (569,33)  (569,24)  (569,20)  (568,33)  (568,22)  (568,18)  (566,18)  (566,35)  (566,32)  (533,14)  (553,32)  (553,77)  (553,68)  (553,54)  (553,41)  (553,28)  (551,34)  (551,104)  (551,95)  (551,75)  (551,56)  (551,43)  (551,30)  (549,36)  (549,72)  (549,58)  (549,45)  (549,32)  (547,36)  (547,72)  (547,58)  (547,45)  (547,32)  (546,45)  (546,34)  (546,34)  (546,30)  (545,43)  (545,32)  (545,28)  (544,41)  (544,30)  (544,26)  (540,32)  (540,68)  (540,54)  (540,41)  (540,28)  (539,30)  (539,30)  (539,26)  (537,35)  (537,26)  (537,22)  (535,33)  (535,22)  (535,18)  (533,18)  (533,35)  (533,32) )

Total verification time: 3.19 second(s)
	Time spent in main process: 2.08 second(s)
	Time spent in child processes: 1.11 second(s)
