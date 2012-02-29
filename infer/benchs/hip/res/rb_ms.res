
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
                    flted_45_458: a::rb2<na,flted_45_458>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_45_457>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_45_456>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    d::rb2<nd,flted_45_455>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_45_458][0=flted_45_457][0=flted_45_456]
                     [0=flted_45_455][0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(flted_46_454,
                                n: res::rb2<n,flted_46_454>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_46_454][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)a::rb2<na,flted_45_458>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_45_457>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_45_456>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  d::rb2<nd,flted_45_455>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_45_458]
                   [0=flted_45_457][0=flted_45_456][0=flted_45_455]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(n_3611,
                              flted_46_3612: res::rb2<n_3611,flted_46_3612>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([3+na+nb+nc+nd=n_3611 & (3+na+nc+
                                 nd)<=n_3611 & 0<=nb & 0<=na & 0<=nd & 0<=nc]
                               [res!=null][0=flted_46_3612]
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
                    flted_87_416: a::rb2<na,flted_87_416>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_87_415>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_87_414>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    d::rb2<nd,flted_87_413>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_87_416][0=flted_87_415][0=flted_87_414]
                     [0=flted_87_413][0<=na][0<=nb][0<=nc][0<=nd]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(flted_88_412,
                                n: res::rb2<n,flted_88_412>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_88_412][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)a::rb2<na,flted_87_416>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_87_415>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_87_414>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  d::rb2<nd,flted_87_413>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_87_416]
                   [0=flted_87_415][0=flted_87_414][0=flted_87_413]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(n_3707,
                              flted_88_3708: res::rb2<n_3707,flted_88_3708>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([res!=null]
                               [3+na+nb+nc+nd=n_3707 & (3+na+nb+
                                 nc)<=n_3707 & 0<=nc & 0<=nb & 0<=nd & 0<=na]
                               [0=flted_88_3708]
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
assert/assume:rb_ms.ss:383: 1:  : failed


assert:rb_ms.ss:384: 1:  : ok


Procedure del_2r$node~node~node SUCCESS

Checking procedure del$node~int... 
assert/assume:rb_ms.ss:512: 4:  : failed


assert/assume:rb_ms.ss:513: 7:  : failed


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
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                    (([0<=cl & cl<=1][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::ref [x]
                                
                                EXISTS(cl2,
                                n1: x'::rb2<n1,cl2>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                                (
                                ([1=cl][0<=cl2 & cl2<=1][0<=n1 & DEL1(n,n1)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_496_112,
                                   n2: x'::rb2<n2,flted_496_112>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                   (
                                   ([0=flted_496_112][0=cl]
                                    [0<=n2 & DEL2(n,n2)]))&
                                   {FLOW,(20,21)=__norm})
                                or EXISTS(cl_113,
                                   n3: x'::rb2<n3,cl_113>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                                   (
                                   ([0<=n3 & DEL3(n,n3)]
                                    [cl=cl_113 & cl_113<=1 & 0<=cl_113]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                  (([0<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::ref [x]
                              
                              EXISTS(flted_496_5460,
                              n2_5461: x'::rb2<n2_5461,flted_496_5460>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([n2_5461<=n & 0<=n & 0<=n2_5461 & (-1+
                                 n)<=n2_5461]
                               [cl=0 & 0<=cl & cl<=1][0=flted_496_5460]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl2_5462,
                                 n1_5463: x'::rb2<n1_5463,cl2_5462>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                                 (
                                 ([1+n1_5463=n & 0<=n & 0<=n1_5463]
                                  [0<=cl2_5462 & cl2_5462<=1]
                                  [cl=1 & 0<=cl & cl<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(cl_5464,
                                 n3_5465: x'::rb2<n3_5465,cl_5464>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                                 (
                                 ([n3_5465<=n & 0<=n & 0<=n3_5465 & (-1+
                                    n)<=n3_5465]
                                  [cl=cl_5464 & cl<=1 & 0<=cl]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(nl_4444:-1+n=n2 & 0<=nl_4444 & (1+nl_4444)<=n2)) --> DEL2(n,n2),
 (-1+n=n2 & 0<=n2) --> DEL2(n,n2),
 (n2=0 & n=0) --> DEL2(n,n2),
 (exists(nl_4444:-1+n=n3 & 0<=nl_4444 & (1+nl_4444)<=n3)) --> DEL3(n,n3),
 (-1+n=n1 & 0<=n1) --> DEL1(n,n1),
 (-1+n=n3 & 0<=n3) --> DEL3(n,n3),
 (n3=0 & n=0) --> DEL3(n,n3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$node~int SUCCESS

Checking procedure del_2$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_333_156,
                    flted_333_157,
                    flted_333_158: a::rb2<na,flted_333_158>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_333_157>@M[Orig][LHSCase]@ rem br[{702}] * 
                    c::rb2<nc,flted_333_156>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_333_158][flted_333_157=0][0=flted_333_156]
                     [null!=b][0<=na][0<=nb & 0!=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(flted_334_155,
                                n: res::rb2<n,flted_334_155>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_334_155][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_333_158>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_333_157>@M[Orig][LHSCase]@ rem br[{702}] * 
                  c::rb2<nc,flted_333_156>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([b!=null][0<=na][1<=nb][0<=nc][0=flted_333_158]
                   [0=flted_333_157][0=flted_333_156]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              false&(([false]))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_2$node~node~node SUCCESS

Checking procedure del_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_293_194,
                    flted_293_195,
                    flted_293_196: a::rb2<na,flted_293_196>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_293_195>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_293_194>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_293_196][0=flted_293_195][0=flted_293_194]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::
                                EXISTS(flted_294_193,
                                n: res::rb2<n,flted_294_193>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_294_193][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_293_196>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_293_195>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_293_194>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_293_196][0=flted_293_195]
                   [0=flted_293_194]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 43::
                              EXISTS(n_6043,
                              flted_294_6044: res::rb2<n_6043,flted_294_6044>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([2+na+nb+nc=n_6043 & 0<=na & (2+nb+
                                 nc)<=n_6043 & 0<=nb & 0<=nc]
                               [res!=null][0=flted_294_6044]
                               [0<=flted_293_194 & flted_293_194<=1]
                               [0<=flted_293_195 & flted_293_195<=1]
                               [0<=flted_293_196 & flted_293_196<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_313_175,
                    flted_313_176,
                    flted_313_177: a::rb2<na,flted_313_177>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_313_176>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_313_175>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_313_177][0=flted_313_176][0=flted_313_175]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 46::
                                EXISTS(flted_314_174,
                                n: res::rb2<n,flted_314_174>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_314_174][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_313_177>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_313_176>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_313_175>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_313_177][0=flted_313_176]
                   [0=flted_313_175]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 46::
                              EXISTS(n_6158,
                              flted_314_6159: res::rb2<n_6158,flted_314_6159>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([2+na+nb+nc=n_6158 & (2+na+nc)<=n_6158 & 
                                 0<=nb & 0<=nc & 0<=na]
                               [res!=null][0=flted_314_6159]
                               [0<=flted_313_175 & flted_313_175<=1]
                               [0<=flted_313_176 & flted_313_176<=1]
                               [0<=flted_313_177 & flted_313_177<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_254_232,
                    flted_254_233,
                    flted_254_234: a::rb2<na,flted_254_234>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_254_233>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_254_232>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_254_234][0=flted_254_233][0=flted_254_232]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                EXISTS(flted_255_231,
                                n: res::rb2<n,flted_255_231>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_255_231][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_254_234>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_254_233>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_254_232>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_254_234][0=flted_254_233]
                   [0=flted_254_232]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              EXISTS(n_6281,
                              flted_255_6282: res::rb2<n_6281,flted_255_6282>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([2+na+nb+nc=n_6281 & (2+na+nc)<=n_6281 & 
                                 0<=nb & 0<=na & 0<=nc]
                               [res!=null][0=flted_255_6282]
                               [0<=flted_254_232 & flted_254_232<=1]
                               [0<=flted_254_233 & flted_254_233<=1]
                               [0<=flted_254_234 & flted_254_234<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_273_213,
                    flted_273_214,
                    flted_273_215: a::rb2<na,flted_273_215>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_273_214>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_273_213>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([0=flted_273_215][0=flted_273_214][0=flted_273_213]
                     [0<=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 40::
                                EXISTS(flted_274_212,
                                n: res::rb2<n,flted_274_212>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_274_212][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_273_215>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_273_214>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_273_213>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([0<=na][0<=nb][0<=nc][0=flted_273_215][0=flted_273_214]
                   [0=flted_273_213]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 40::
                              EXISTS(n_6396,
                              flted_274_6397: res::rb2<n_6396,flted_274_6397>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([2+na+nb+nc=n_6396 & (2+na+nc)<=n_6396 & 
                                 0<=nb & 0<=nc & 0<=na]
                               [res!=null][0=flted_274_6397]
                               [0<=flted_273_213 & flted_273_213<=1]
                               [0<=flted_273_214 & flted_273_214<=1]
                               [0<=flted_273_215 & flted_273_215<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer [a,b,c,d,res]
              EBase exists (Expl)(Impl)[na; nb; nc; 
                    nd](ex)
                           EXISTS(flted_207_304,flted_207_305,flted_207_306,
                           flted_207_307: a::rb2<na,flted_207_307>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           b::rb2<nb,flted_207_306>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           c::rb2<nc,flted_207_305>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           d::rb2<nd,flted_207_304>@M[Orig][LHSCase]@ rem br[{704,702}]&
                           (
                           ([0=flted_207_307][0=flted_207_306]
                            [0=flted_207_305][0=flted_207_304][0=color]
                            [0<=na][0<=nb][0<=nc][0<=nd]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_208_308,flted_208_309,
                              flted_208_310,
                              flted_208_311: a::rb2<na,flted_208_311>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              b::rb2<nb,flted_208_310>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              c::rb2<nc,flted_208_309>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              d::rb2<nd,flted_208_308>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([0=flted_208_311][0=flted_208_310]
                               [0=flted_208_309][0=flted_208_308][1=color]
                               [0<=na][0<=nb][0<=nc][0<=nd]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                
                                EXISTS(flted_209_302,
                                n1: res::rb2<n1,flted_209_302>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_209_302][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_210_303,
                                   n2: res::rb2<n2,flted_210_303>@M[Orig][LHSCase]@ rem br[{703}]&
                                   (
                                   ([flted_210_303=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)
                         a::rb2<na,flted_207_307>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         b::rb2<nb,flted_207_306>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         c::rb2<nc,flted_207_305>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         d::rb2<nd,flted_207_304>@M[Orig][LHSCase]@ rem br[{704,702}]&
                         (
                         ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_207_307]
                          [0=flted_207_306][0=flted_207_305][0=flted_207_304]
                          [0=color]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_208_311>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            b::rb2<nb,flted_208_310>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            c::rb2<nc,flted_208_309>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            d::rb2<nd,flted_208_308>@M[Orig][LHSCase]@ rem br[{704,702}]&
                            (
                            ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_208_311]
                             [0=flted_208_310][0=flted_208_309]
                             [0=flted_208_308][1=color]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              
                              EXISTS(n1_6693,
                              flted_209_6694: res::rb2<n1_6693,flted_209_6694>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([(0<=flted_207_307 & flted_207_307<=1 & 
                                 0<=na & 0<=flted_207_306 & 
                                 flted_207_306<=1 & 0<=nb & 
                                 0<=flted_207_305 & flted_207_305<=1 & 
                                 0<=nc & 0<=flted_207_304 & 
                                 flted_207_304<=1 & 0<=nd | 
                                 0<=flted_208_311 & flted_208_311<=1 & 
                                 0<=na & 0<=flted_208_310 & 
                                 flted_208_310<=1 & 0<=nb & 
                                 0<=flted_208_309 & flted_208_309<=1 & 
                                 0<=nc & 0<=flted_208_308 & 
                                 flted_208_308<=1 & 0<=nd) & n1_6693=3+na+nb+
                                 nc+nd & 0<=nd & 0<=na & 0<=nb & 0<=nc]
                               [res!=null][0=flted_209_6694][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_6695,
                                 flted_210_6696: res::rb2<n2_6695,flted_210_6696>@M[Orig][LHSCase]@ rem br[{703}]&
                                 (
                                 ([(0<=flted_207_307 & flted_207_307<=1 & 
                                    0<=na & 0<=flted_207_306 & 
                                    flted_207_306<=1 & 0<=nb & 
                                    0<=flted_207_305 & flted_207_305<=1 & 
                                    0<=nc & 0<=flted_207_304 & 
                                    flted_207_304<=1 & 0<=nd | 
                                    0<=flted_208_311 & flted_208_311<=1 & 
                                    0<=na & 0<=flted_208_310 & 
                                    flted_208_310<=1 & 0<=nb & 
                                    0<=flted_208_309 & flted_208_309<=1 & 
                                    0<=nc & 0<=flted_208_308 & 
                                    flted_208_308<=1 & 0<=nd) & n2_6695=3+na+
                                    nb+nc+nd & 0<=nb & 0<=na & 0<=nd & 0<=nc]
                                  [res!=null][1=flted_210_6696][1=color]))&
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
                           EXISTS(flted_232_259,flted_232_260,flted_232_261,
                           flted_232_262: a::rb2<na,flted_232_262>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           b::rb2<nb,flted_232_261>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           c::rb2<nc,flted_232_260>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           d::rb2<nd,flted_232_259>@M[Orig][LHSCase]@ rem br[{704,702}]&
                           (
                           ([0=flted_232_262][0=flted_232_261]
                            [0=flted_232_260][0=flted_232_259][0=color]
                            [0<=na][0<=nb][0<=nc][0<=nd]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_233_263,flted_233_264,
                              flted_233_265,
                              flted_233_266: a::rb2<na,flted_233_266>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              b::rb2<nb,flted_233_265>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              c::rb2<nc,flted_233_264>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              d::rb2<nd,flted_233_263>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([0=flted_233_266][0=flted_233_265]
                               [0=flted_233_264][0=flted_233_263][1=color]
                               [0<=na][0<=nb][0<=nc][0<=nd]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 33::
                                
                                EXISTS(flted_234_257,
                                n1: res::rb2<n1,flted_234_257>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_234_257][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_235_258,
                                   n2: res::rb2<n2,flted_235_258>@M[Orig][LHSCase]@ rem br[{703}]&
                                   (
                                   ([flted_235_258=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; nc; 
                  nd](ex)
                         a::rb2<na,flted_232_262>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         b::rb2<nb,flted_232_261>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         c::rb2<nc,flted_232_260>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         d::rb2<nd,flted_232_259>@M[Orig][LHSCase]@ rem br[{704,702}]&
                         (
                         ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_232_262]
                          [0=flted_232_261][0=flted_232_260][0=flted_232_259]
                          [0=color]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_233_266>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            b::rb2<nb,flted_233_265>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            c::rb2<nc,flted_233_264>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            d::rb2<nd,flted_233_263>@M[Orig][LHSCase]@ rem br[{704,702}]&
                            (
                            ([0<=na][0<=nb][0<=nc][0<=nd][0=flted_233_266]
                             [0=flted_233_265][0=flted_233_264]
                             [0=flted_233_263][1=color]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 33::
                              
                              EXISTS(n1_7000,
                              flted_234_7001: res::rb2<n1_7000,flted_234_7001>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([(0<=flted_232_262 & flted_232_262<=1 & 
                                 0<=na & 0<=flted_232_261 & 
                                 flted_232_261<=1 & 0<=nb & 
                                 0<=flted_232_260 & flted_232_260<=1 & 
                                 0<=nc & 0<=flted_232_259 & 
                                 flted_232_259<=1 & 0<=nd | 
                                 0<=flted_233_266 & flted_233_266<=1 & 
                                 0<=na & 0<=flted_233_265 & 
                                 flted_233_265<=1 & 0<=nb & 
                                 0<=flted_233_264 & flted_233_264<=1 & 
                                 0<=nc & 0<=flted_233_263 & 
                                 flted_233_263<=1 & 0<=nd) & n1_7000=3+na+nb+
                                 nc+nd & 0<=na & 0<=nc & 0<=nb & 0<=nd]
                               [res!=null][0=flted_234_7001][0=color]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_7002,
                                 flted_235_7003: res::rb2<n2_7002,flted_235_7003>@M[Orig][LHSCase]@ rem br[{703}]&
                                 (
                                 ([res!=null]
                                  [(0<=flted_232_262 & flted_232_262<=1 & 
                                    0<=na & 0<=flted_232_261 & 
                                    flted_232_261<=1 & 0<=nb & 
                                    0<=flted_232_260 & flted_232_260<=1 & 
                                    0<=nc & 0<=flted_232_259 & 
                                    flted_232_259<=1 & 0<=nd | 
                                    0<=flted_233_266 & flted_233_266<=1 & 
                                    0<=na & 0<=flted_233_265 & 
                                    flted_233_265<=1 & 0<=nb & 
                                    0<=flted_233_264 & flted_233_264<=1 & 
                                    0<=nc & 0<=flted_233_263 & 
                                    flted_233_263<=1 & 0<=nd) & n2_7002=3+na+
                                    nb+nc+nd & 0<=na & 0<=nb & 0<=nc & 0<=nd]
                                  [1=flted_235_7003][1=color]))&
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
                           EXISTS(flted_153_374,
                           flted_153_375: a::rb2<na,flted_153_375>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                           b::rb2<nb,Anon_15>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                           c::rb2<nc,flted_153_374>@M[Orig][LHSCase]@ rem br[{703}]&
                           (
                           ([0=flted_153_375][flted_153_374=1][0=color]
                            [null!=c][0<=na][0<=nb][Anon_15<=1 & 0<=Anon_15]
                            [0<=nc & 0!=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_154_376,
                              flted_154_377: a::rb2<na,flted_154_377>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                              b::rb2<nb,Anon_16>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                              c::rb2<nc,flted_154_376>@M[Orig][LHSCase]@ rem br[{703}]&
                              (
                              ([0=flted_154_377][flted_154_376=1][1=color]
                               [null!=c][0<=na][0<=nb]
                               [Anon_16<=1 & 0<=Anon_16][0<=nc & 0!=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::
                                
                                EXISTS(flted_155_372,
                                n1: res::rb2<n1,flted_155_372>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_155_372][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_156_373,
                                   n2: res::rb2<n2,flted_156_373>@M[Orig][LHSCase]@ rem br[{703}]&
                                   (
                                   ([flted_156_373=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15; na; nb; Anon_16; 
                  nc](ex)
                         a::rb2<na,flted_153_375>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                         b::rb2<nb,Anon_15>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                         c::rb2<nc,flted_153_374>@M[Orig][LHSCase]@ rem br[{703}]&
                         (
                         ([c!=null][0<=na][0<=nb][1<=nc][0=flted_153_375]
                          [1=flted_153_374][0=color][Anon_15<=1 & 0<=Anon_15]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_154_377>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                            b::rb2<nb,Anon_16>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                            c::rb2<nc,flted_154_376>@M[Orig][LHSCase]@ rem br[{703}]&
                            (
                            ([c!=null][0<=na][0<=nb][1<=nc][0=flted_154_377]
                             [1=flted_154_376][1=color]
                             [Anon_16<=1 & 0<=Anon_16]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::
                              
                              EXISTS(n1_7522,
                              flted_155_7523: res::rb2<n1_7522,flted_155_7523>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_153_375 & flted_153_375<=1 & 
                                 0<=na & 0<=Anon_15 & Anon_15<=1 & 0<=nb & 
                                 0<=flted_153_374 & flted_153_374<=1 & 
                                 0<=nc | 0<=flted_154_377 & 
                                 flted_154_377<=1 & 0<=na & 0<=Anon_16 & 
                                 Anon_16<=1 & 0<=nb & 0<=flted_154_376 & 
                                 flted_154_376<=1 & 0<=nc) & 2+na+nb+
                                 nc=n1_7522 & 1<=nc & (2+nb+nc)<=n1_7522 & 
                                 0<=nb]
                               [res!=null][c!=null][0=color]
                               [0=flted_155_7523]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_7524,
                                 flted_156_7525: res::rb2<n2_7524,flted_156_7525>@M[Orig][LHSCase]@ rem br[{703}]&
                                 (
                                 ([Anon_16<=1 & 0<=Anon_16 & 
                                    (0<=flted_153_375 & flted_153_375<=1 & 
                                    0<=na & 0<=Anon_15 & Anon_15<=1 & 
                                    0<=nb & 0<=flted_153_374 & 
                                    flted_153_374<=1 & 0<=nc | 
                                    0<=flted_154_377 & flted_154_377<=1 & 
                                    0<=na & 0<=Anon_16 & Anon_16<=1 & 
                                    0<=nb & 0<=flted_154_376 & 
                                    flted_154_376<=1 & 0<=nc) & 2+na+nb+
                                    nc=n2_7524 & 1<=nc & (2+nb+
                                    nc)<=n2_7524 & 0<=nb]
                                  [res!=null][c!=null][1=color]
                                  [1=flted_156_7525]))&
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
                           EXISTS(flted_180_345,
                           flted_180_346: a::rb2<na,flted_180_346>@M[Orig][LHSCase]@ rem br[{703}] * 
                           b::rb2<nb,Anon_19>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                           c::rb2<nc,flted_180_345>@M[Orig][LHSCase]@ rem br[{704,702}]&
                           (
                           ([flted_180_346=1][0=flted_180_345][0=color]
                            [null!=a][0<=na & 0!=na][0<=nb]
                            [Anon_19<=1 & 0<=Anon_19][0<=nc]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(flted_181_347,
                              flted_181_348: a::rb2<na,flted_181_348>@M[Orig][LHSCase]@ rem br[{703}] * 
                              b::rb2<nb,Anon_20>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                              c::rb2<nc,flted_181_347>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([flted_181_348=1][0=flted_181_347][1=color]
                               [null!=a][0<=na & 0!=na][0<=nb]
                               [Anon_20<=1 & 0<=Anon_20][0<=nc]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                
                                EXISTS(flted_182_343,
                                n1: res::rb2<n1,flted_182_343>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_182_343][0=color][0<=n1]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_183_344,
                                   n2: res::rb2<n2,flted_183_344>@M[Orig][LHSCase]@ rem br[{703}]&
                                   (
                                   ([flted_183_344=1][1=color][0<=n2 & 0!=n2]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; na; nb; Anon_20; 
                  nc](ex)
                         a::rb2<na,flted_180_346>@M[Orig][LHSCase]@ rem br[{703}] * 
                         b::rb2<nb,Anon_19>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                         c::rb2<nc,flted_180_345>@M[Orig][LHSCase]@ rem br[{704,702}]&
                         (
                         ([a!=null][1<=na][0<=nb][0<=nc][1=flted_180_346]
                          [0=flted_180_345][0=color][Anon_19<=1 & 0<=Anon_19]
                          ))&
                         {FLOW,(20,21)=__norm}
                         or a::rb2<na,flted_181_348>@M[Orig][LHSCase]@ rem br[{703}] * 
                            b::rb2<nb,Anon_20>@M[Orig][LHSCase]@ rem br[{704,703,702}] * 
                            c::rb2<nc,flted_181_347>@M[Orig][LHSCase]@ rem br[{704,702}]&
                            (
                            ([a!=null][1<=na][0<=nb][0<=nc][1=flted_181_348]
                             [0=flted_181_347][1=color]
                             [Anon_20<=1 & 0<=Anon_20]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              
                              EXISTS(n1_8060,
                              flted_182_8061: res::rb2<n1_8060,flted_182_8061>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_180_346 & flted_180_346<=1 & 
                                 0<=na & 0<=Anon_19 & Anon_19<=1 & 0<=nb & 
                                 0<=flted_180_345 & flted_180_345<=1 & 
                                 0<=nc | 0<=flted_181_348 & 
                                 flted_181_348<=1 & 0<=na & 0<=Anon_20 & 
                                 Anon_20<=1 & 0<=nb & 0<=flted_181_347 & 
                                 flted_181_347<=1 & 0<=nc) & 2+na+nb+
                                 nc=n1_8060 & 1<=na & (2+na+nb)<=n1_8060 & 
                                 0<=nb]
                               [res!=null][a!=null][0=color]
                               [0=flted_182_8061]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n2_8062,
                                 flted_183_8063: res::rb2<n2_8062,flted_183_8063>@M[Orig][LHSCase]@ rem br[{703}]&
                                 (
                                 ([Anon_20<=1 & 0<=Anon_20 & 
                                    (0<=flted_180_346 & flted_180_346<=1 & 
                                    0<=na & 0<=Anon_19 & Anon_19<=1 & 
                                    0<=nb & 0<=flted_180_345 & 
                                    flted_180_345<=1 & 0<=nc | 
                                    0<=flted_181_348 & flted_181_348<=1 & 
                                    0<=na & 0<=Anon_20 & Anon_20<=1 & 
                                    0<=nb & 0<=flted_181_347 & 
                                    flted_181_347<=1 & 0<=nc) & 2+na+nb+
                                    nc=n2_8062 & 1<=na & (2+na+
                                    nb)<=n2_8062 & 0<=nb]
                                  [res!=null][a!=null][1=color]
                                  [1=flted_183_8063]))&
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
                    Anon_21](ex)x::rb2<n,Anon_21>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                    (([0<=n][Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 111::
                                EXISTS(Anon_22,
                                n1: res::rb2<n1,Anon_22>@M[Orig][LHSCase]@ rem br[{703,702}]&
                                (
                                ([null!=res][0!=n1 & 0<=n1 & INS(n,n1)]
                                 [Anon_22<=1 & 0<=Anon_22]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  Anon_21](ex)x::rb2<n,Anon_21>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                  (([0<=n][Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 111::
                              EXISTS(Anon_8758,
                              n1_8759: res::rb2<n1_8759,Anon_8758>@M[Orig][LHSCase]@ rem br[{703,702}]&
                              (
                              ([1=n1_8759 & 0!=n1_8759 & 0<=n1_8759]
                               [n=0 & 0<=n][null!=res]
                               [0<=Anon_8758 & Anon_8758<=1]
                               [Anon_21<=1 & 0<=Anon_21]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & n1=1) --> INS(n,n1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure is_black$node... 
!!! OLD SPECS: ((None,[]),EInfer [n1,n2]
              EBase exists (Expl)(Impl)[n; 
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                    (([0<=n][cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::
                                
                                EXISTS(cl_395: x::rb2<n1,cl_395>@M[Orig][LHSCase]@ rem br[{703}]&
                                (
                                ([!(res)][cl=cl_395 & cl=1][0<=n1 & 0!=n1]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl_396: x::rb2<n2,cl_396>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                   (([res][cl=cl_396 & cl=0][0<=n2]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                  (([0<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::
                              
                              EXISTS(n2_8960,
                              cl_8961: x::rb2<n2_8960,cl_8961>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([n=n2_8960 & 1<=n & 0<=n][x!=null]
                               [0=cl & 0<=cl & cl<=1][0=cl_8961][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_8962,
                                 cl_8963: x::rb2<n1_8962,cl_8963>@M[Orig][LHSCase]@ rem br[{703}]&
                                 (
                                 ([n=n1_8962 & 1<=n1_8962 & 0<=n][x!=null]
                                  [1=cl & 0<=cl & cl<=1][1=cl_8963][!(res)]))&
                                 {FLOW,(20,21)=__norm})
                              or true&(
                                 ([null=x][0=n & 0<=n][0=cl & 0<=cl & cl<=1]
                                  [0=n2][res]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
!!! OLD SPECS: ((None,[]),EInfer [n1,n2]
              EBase exists (Expl)(Impl)[n; 
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                    (([0<=n][cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 14::
                                
                                EXISTS(cl_401: x::rb2<n1,cl_401>@M[Orig][LHSCase]@ rem br[{703}]&
                                (
                                ([res][cl=cl_401 & cl=1][0<=n1 & 0!=n1]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl_402: x::rb2<n2,cl_402>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                   (([!(res)][cl=cl_402 & cl=0][0<=n2]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                  (([0<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 14::
                              
                              EXISTS(n2_9164,
                              cl_9165: x::rb2<n2_9164,cl_9165>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([x!=null][n=n2_9164 & 1<=n & 0<=n]
                               [0=cl & 0<=cl & cl<=1][0=cl_9165][!(res)]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_9166,
                                 cl_9167: x::rb2<n1_9166,cl_9167>@M[Orig][LHSCase]@ rem br[{703}]&
                                 (
                                 ([n=n1_9166 & 1<=n1_9166 & 0<=n][x!=null]
                                  [1=cl & 0<=cl & cl<=1][1=cl_9167][res]))&
                                 {FLOW,(20,21)=__norm})
                              or true&(
                                 ([null=x][0=n & 0<=n][0=cl & 0<=cl & cl<=1]
                                  [0=n2][!(res)]))&
                                 {FLOW,(20,21)=__norm}
                              )
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
                    cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{703,702}]&(
                    ([null!=x][0<=cl & cl<=1][0<=n & 0!=n]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 63::ref [x]
                                
                                EXISTS(cl2,
                                n1: x'::rb2<n1,cl2>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                                (
                                ([1=cl][0<=cl2 & cl2<=1][0<=n1 & RMVM1(n,n1)]
                                 ))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_411_116,
                                   n2: x'::rb2<n2,flted_411_116>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                   (
                                   ([0=flted_411_116][0=cl]
                                    [0<=n2 & RMVM2(n,n2)]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  cl](ex)x::rb2<n,cl>@M[Orig][LHSCase]@ rem br[{703,702}]&(
                  ([x!=null][1<=n][0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 63::ref [x]
                              
                              EXISTS(cl2_9719,
                              n1_9720: x'::rb2<n1_9720,cl2_9719>@M[Orig][LHSCase]@ rem br[{704,703,702}]&
                              (
                              ([1+n1_9720=n & 0<=n & 0<=n1_9720]
                               [0<=cl2_9719 & cl2_9719<=1]
                               [cl=1 & 0<=cl & cl<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_411_9721,
                                 n2_9722: x'::rb2<n2_9722,flted_411_9721>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                 (
                                 ([1+n2_9722=n & 0<=n & 0<=n2_9722]
                                  [cl=0 & 0<=cl & cl<=1][0=flted_411_9721]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(nl_9340:-1+n=n2 & 0<=nl_9340 & (1+nl_9340)<=n2)) --> RMVM2(n,n2),
 (-1+n=n1 & 0<=n1) --> RMVM1(n,n1),
 (-1+n=n2 & 0<=n2) --> RMVM2(n,n2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[na; nb; nc](ex)EXISTS(flted_24_477,
                    flted_24_478,
                    flted_24_479: a::rb2<na,flted_24_479>@M[Orig][LHSCase]@ rem br[{703}] * 
                    b::rb2<nb,flted_24_478>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_24_477>@M[Orig][LHSCase]@ rem br[{704,702}]&
                    (
                    ([flted_24_479=1][0=flted_24_478][0=flted_24_477]
                     [null!=a][0<=na & 0!=na][0<=nb][0<=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(flted_25_476,
                                n: res::rb2<n,flted_25_476>@M[Orig][LHSCase]@ rem br[{702}]&
                                (([flted_25_476=0][null!=res][0<=n & 0!=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_24_479>@M[Orig][LHSCase]@ rem br[{703}] * 
                  b::rb2<nb,flted_24_478>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_24_477>@M[Orig][LHSCase]@ rem br[{704,702}]&
                  (
                  ([a!=null][1<=na][0<=nb][0<=nc][1=flted_24_479]
                   [0=flted_24_478][0=flted_24_477]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(n_9836,
                              flted_25_9837: res::rb2<n_9836,flted_25_9837>@M[Orig][LHSCase]@ rem br[{702}]&
                              (
                              ([2+na+nb+nc=n_9836 & 0<=na & (3+nb+
                                 nc)<=n_9836 & 0<=nb & 0<=nc]
                               [res!=null][a!=null][0=flted_25_9837]
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
                    flted_66_437: a::rb2<na,flted_66_437>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    b::rb2<nb,flted_66_436>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                    c::rb2<nc,flted_66_435>@M[Orig][LHSCase]@ rem br[{703}]&(
                    ([0=flted_66_437][0=flted_66_436][flted_66_435=1]
                     [null!=c][0<=na][0<=nb][0<=nc & 0!=nc]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(flted_67_434,
                                n: res::rb2<n,flted_67_434>@M[Orig][LHSCase]@ rem br[{704,702}]&
                                (([0=flted_67_434][0<=n]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[na; nb; 
                  nc](ex)a::rb2<na,flted_66_437>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  b::rb2<nb,flted_66_436>@M[Orig][LHSCase]@ rem br[{704,702}] * 
                  c::rb2<nc,flted_66_435>@M[Orig][LHSCase]@ rem br[{703}]&(
                  ([c!=null][0<=na][0<=nb][1<=nc][0=flted_66_437]
                   [0=flted_66_436][1=flted_66_435]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(n_9951,
                              flted_67_9952: res::rb2<n_9951,flted_67_9952>@M[Orig][LHSCase]@ rem br[{704,702}]&
                              (
                              ([2+na+nb+nc=n_9951 & (2+na+nc)<=n_9951 & 
                                 0<=nb & 1<=nc & 0<=nc & 0<=na]
                               [res!=null][c!=null][0=flted_67_9952]
                               [0<=flted_66_435 & flted_66_435<=1]
                               [0<=flted_66_436 & flted_66_436<=1]
                               [0<=flted_66_437 & flted_66_437<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 3656 invocations 
304 false contexts at: ( (484,3)  (484,10)  (481,4)  (481,11)  (476,22)  (476,29)  (475,26)  (475,71)  (475,56)  (475,42)  (475,34)  (475,22)  (475,22)  (470,26)  (470,33)  (469,30)  (469,100)  (469,85)  (469,65)  (469,46)  (469,38)  (469,26)  (469,26)  (465,28)  (465,35)  (464,32)  (464,62)  (464,48)  (464,40)  (464,28)  (464,28)  (460,28)  (460,35)  (459,32)  (459,62)  (459,48)  (459,40)  (459,28)  (459,28)  (457,39)  (457,28)  (457,28)  (457,24)  (456,37)  (456,26)  (456,22)  (454,33)  (454,22)  (454,18)  (450,20)  (450,27)  (447,22)  (447,29)  (446,26)  (446,56)  (446,42)  (446,34)  (446,22)  (446,22)  (444,22)  (444,22)  (444,18)  (442,27)  (442,18)  (442,14)  (440,25)  (440,14)  (440,10)  (438,6)  (438,22)  (438,19)  (727,14)  (724,16)  (720,24)  (717,28)  (717,35)  (716,32)  (716,71)  (716,57)  (716,49)  (716,28)  (716,28)  (712,28)  (712,35)  (711,44)  (711,28)  (710,43)  (710,28)  (710,28)  (708,37)  (708,28)  (708,24)  (703,24)  (703,31)  (702,28)  (702,85)  (702,65)  (702,46)  (702,38)  (702,24)  (702,24)  (698,24)  (698,31)  (697,40)  (697,24)  (696,39)  (696,24)  (696,24)  (694,33)  (694,24)  (694,20)  (681,12)  (678,16)  (674,24)  (670,30)  (670,37)  (669,34)  (669,95)  (669,75)  (669,56)  (669,43)  (669,30)  (669,30)  (665,30)  (665,37)  (664,46)  (664,30)  (663,45)  (663,30)  (663,30)  (661,39)  (661,30)  (661,26)  (654,26)  (654,33)  (653,30)  (653,73)  (653,59)  (653,46)  (653,26)  (653,26)  (649,26)  (649,33)  (648,42)  (648,26)  (647,41)  (647,26)  (647,26)  (645,35)  (645,26)  (645,22)  (585,14)  (606,30)  (606,75)  (606,60)  (606,46)  (606,38)  (606,26)  (604,32)  (604,102)  (604,87)  (604,67)  (604,48)  (604,40)  (604,28)  (601,36)  (601,66)  (601,52)  (601,44)  (601,32)  (599,36)  (599,66)  (599,52)  (599,44)  (599,32)  (598,45)  (598,34)  (598,34)  (598,30)  (596,41)  (596,30)  (596,26)  (595,39)  (595,28)  (595,24)  (591,30)  (591,60)  (591,46)  (591,38)  (591,26)  (590,28)  (590,28)  (590,24)  (588,33)  (588,24)  (588,20)  (587,33)  (587,22)  (587,18)  (585,18)  (585,34)  (585,31)  (558,14)  (577,34)  (577,79)  (577,70)  (577,56)  (577,43)  (577,30)  (575,32)  (575,102)  (575,93)  (575,73)  (575,54)  (575,41)  (575,28)  (573,34)  (573,70)  (573,56)  (573,43)  (573,30)  (571,34)  (571,70)  (571,56)  (571,43)  (571,30)  (570,43)  (570,32)  (570,32)  (570,28)  (569,41)  (569,30)  (569,26)  (568,39)  (568,28)  (568,24)  (564,30)  (564,64)  (564,50)  (564,37)  (564,26)  (563,28)  (563,28)  (563,24)  (561,33)  (561,24)  (561,20)  (560,33)  (560,22)  (560,18)  (558,18)  (558,35)  (558,32)  (525,14)  (545,32)  (545,77)  (545,68)  (545,54)  (545,41)  (545,28)  (543,34)  (543,104)  (543,95)  (543,75)  (543,56)  (543,43)  (543,30)  (541,36)  (541,72)  (541,58)  (541,45)  (541,32)  (539,36)  (539,72)  (539,58)  (539,45)  (539,32)  (538,45)  (538,34)  (538,34)  (538,30)  (537,43)  (537,32)  (537,28)  (536,41)  (536,30)  (536,26)  (532,32)  (532,68)  (532,54)  (532,41)  (532,28)  (531,30)  (531,30)  (531,26)  (529,35)  (529,26)  (529,22)  (527,33)  (527,22)  (527,18)  (525,18)  (525,35)  (525,32) )

Total verification time: 3.11 second(s)
	Time spent in main process: 2. second(s)
	Time spent in child processes: 1.11 second(s)
