
Processing file "rb_m.ss"
Parsing rb_m.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure case_2$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_44_343,flted_44_344,flted_44_345,
                    flted_44_346: a::rb1<flted_44_346>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_44_345>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_44_344>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_44_343>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_44_346][0=flted_44_345][0=flted_44_344]
                     [0=flted_44_343]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_44_346>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_44_345>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_44_344>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_44_343>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_44_346][0=flted_44_345][0=flted_44_344]
                   [0=flted_44_343]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(cl_3123: res::rb1<cl_3123>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_3123]
                               [0<=flted_44_343 & flted_44_343<=1]
                               [0<=flted_44_344 & flted_44_344<=1]
                               [0<=flted_44_345 & flted_44_345<=1]
                               [0<=flted_44_346 & flted_44_346<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_81_313,flted_81_314,flted_81_315,
                    flted_81_316: a::rb1<flted_81_316>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_81_315>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_81_314>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_81_313>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_81_316][0=flted_81_315][0=flted_81_314]
                     [0=flted_81_313]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_81_316>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_81_315>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_81_314>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_81_313>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_81_316][0=flted_81_315][0=flted_81_314]
                   [0=flted_81_313]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(cl_3203: res::rb1<cl_3203>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_3203]
                               [0<=flted_81_313 & flted_81_313<=1]
                               [0<=flted_81_314 & flted_81_314<=1]
                               [0<=flted_81_315 & flted_81_315<=1]
                               [0<=flted_81_316 & flted_81_316<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure del$node~int... 
!!! REL :  DEL1(cl3,cl)
!!! POST:  0=cl & 0=cl3
!!! PRE :  true
!!! REL :  DEL2(cl2,cl)
!!! POST:  0=cl2 & 1=cl
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,DEL1,DEL2]
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 79::ref [x]
                                
                                EXISTS(cl2: x'::rb1<cl2>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([1=cl & 0<=cl2 & cl2<=1 & DEL2(cl2,cl)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl3: x'::rb1<cl3>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (
                                   ([0=cl & 0<=cl3 & cl3<=1 & DEL1(cl3,cl)]))&
                                   {FLOW,(20,21)=__norm})
                                or EXISTS(cl_111: x'::rb1<cl_111>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (([cl=cl_111 & cl_111<=1 & 0<=cl_111]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 79::ref [x]
                              
                              EXISTS(cl3_4326: x'::rb1<cl3_4326>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([0=cl3_4326 & 0<=cl3_4326 & cl3_4326<=1]
                               [cl=0 & 0<=cl & cl<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl2_4327: x'::rb1<cl2_4327>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([cl=1 & 0<=cl & cl<=1]
                                  [0=cl2_4327 & 0<=cl2_4327 & cl2_4327<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(cl_4328: x'::rb1<cl_4328>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (([cl=cl_4328 & cl<=1 & 0<=cl]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (cl=0 & cl3=0) --> DEL1(cl3,cl),
 (cl3=0 & cl=0) --> DEL1(cl3,cl),
 (cl2=0 & cl=1) --> DEL2(cl2,cl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del$node~int SUCCESS

Checking procedure del_2$node~node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ b!=null, b!=null, b!=null, b!=null, b!=null, b!=null, b!=null]
!!! OLD SPECS: ((None,[]),EInfer [res,b]
              EBase EXISTS(flted_363_136,flted_363_137,
                    flted_363_138: a::rb1<flted_363_138>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_363_137>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_363_136>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_363_138][0=flted_363_137][0=flted_363_136]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_363_138>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_363_137>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_363_136>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_363_138][0=flted_363_137][0=flted_363_136]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][b!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              
                              EXISTS(v_5169,flted_14_5170,l_5171,r_5172,
                              cl_5173: b::node<v_5169,flted_14_5170,l_5171,r_5172>@M[Orig][] * 
                              res::rb1<cl_5173>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][b!=null][null=r_5172][null=l_5171]
                               [0=flted_14_5170][0=cl_5173]
                               [0<=flted_363_136 & flted_363_136<=1]
                               [0<=flted_363_137 & flted_363_137<=1]
                               [0<=flted_363_138 & flted_363_138<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_5174,flted_14_5175,l_5176,r_5177,
                                 cl_5178: b::node<v_5174,flted_14_5175,l_5176,r_5177>@M[Orig][] * 
                                 res::rb1<cl_5178>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_5176!=null][res!=null][b!=null]
                                  [null=r_5177][0=cl_5178][0=flted_14_5175]
                                  [0<=flted_363_136 & flted_363_136<=1]
                                  [0<=flted_363_137 & flted_363_137<=1]
                                  [0<=flted_363_138 & flted_363_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5179,flted_14_5180,l_5181,r_5182,
                                 cl_5183: b::node<v_5179,flted_14_5180,l_5181,r_5182>@M[Orig][] * 
                                 res::rb1<cl_5183>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_5182!=null][res!=null][b!=null]
                                  [null=l_5181][0=cl_5183][0=flted_14_5180]
                                  [0<=flted_363_136 & flted_363_136<=1]
                                  [0<=flted_363_137 & flted_363_137<=1]
                                  [0<=flted_363_138 & flted_363_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5184,flted_14_5185,l_5186,r_5187,
                                 cl_5188: b::node<v_5184,flted_14_5185,l_5186,r_5187>@M[Orig][] * 
                                 res::rb1<cl_5188>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_5187!=null][b!=null][l_5186!=null]
                                  [res!=null][0=flted_14_5185][0=cl_5188]
                                  [0<=flted_363_136 & flted_363_136<=1]
                                  [0<=flted_363_137 & flted_363_137<=1]
                                  [0<=flted_363_138 & flted_363_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5189,flted_14_5190,r_5191,l_5192,
                                 v_5193,flted_13_5194,l_5195,r_5196,
                                 cl_5197: b::node<v_5189,flted_14_5190,l_5192,r_5191>@M[Orig][] * 
                                 l_5192::node<v_5193,flted_13_5194,l_5195,r_5196>@M[Orig][] * 
                                 res::rb1<cl_5197>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][b!=null][l_5192!=null]
                                  [null=r_5191][0=flted_14_5190][0=cl_5197]
                                  [1=flted_13_5194]
                                  [0<=flted_363_136 & flted_363_136<=1]
                                  [0<=flted_363_137 & flted_363_137<=1]
                                  [0<=flted_363_138 & flted_363_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5198,flted_14_5199,r_5200,l_5201,
                                 v_5202,flted_13_5203,l_5204,r_5205,
                                 cl_5206: b::node<v_5198,flted_14_5199,l_5201,r_5200>@M[Orig][] * 
                                 l_5201::node<v_5202,flted_13_5203,l_5204,r_5205>@M[Orig][] * 
                                 res::rb1<cl_5206>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_5201!=null][r_5200!=null][res!=null]
                                  [b!=null][1=flted_13_5203][0=cl_5206]
                                  [0=flted_14_5199]
                                  [0<=flted_363_136 & flted_363_136<=1]
                                  [0<=flted_363_137 & flted_363_137<=1]
                                  [0<=flted_363_138 & flted_363_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5207,flted_14_5208,l_5209,r_5210,
                                 cl_5211: b::node<v_5207,flted_14_5208,l_5209,r_5210>@M[Orig][] * 
                                 res::rb1<cl_5211>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][r_5210!=null][b!=null]
                                  [0=flted_14_5208][0=cl_5211]
                                  [0<=flted_363_136 & flted_363_136<=1]
                                  [0<=flted_363_137 & flted_363_137<=1]
                                  [0<=flted_363_138 & flted_363_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_2$node~node~node SUCCESS

Checking procedure del_2r$node~node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ b!=null, b!=null, b!=null, b!=null, b!=null, b!=null, b!=null]
!!! OLD SPECS: ((None,[]),EInfer [a,b,res]
              EBase EXISTS(flted_391_120,flted_391_121,
                    flted_391_122: a::rb1<flted_391_122>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_391_121>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_391_120>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_391_122][0=flted_391_121][0=flted_391_120]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_391_122>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_391_121>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_391_120>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_391_122][0=flted_391_121][0=flted_391_120]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][b!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 59::
                              
                              EXISTS(v_6079,flted_14_6080,l_6081,r_6082,
                              cl_6083: b::node<v_6079,flted_14_6080,l_6081,r_6082>@M[Orig][] * 
                              res::rb1<cl_6083>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([b!=null][res!=null][null=r_6082][null=l_6081]
                               [0=cl_6083][0=flted_14_6080]
                               [0<=flted_391_120 & flted_391_120<=1]
                               [0<=flted_391_121 & flted_391_121<=1]
                               [0<=flted_391_122 & flted_391_122<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_6084,flted_14_6085,l_6086,r_6087,
                                 cl_6088: b::node<v_6084,flted_14_6085,l_6086,r_6087>@M[Orig][] * 
                                 res::rb1<cl_6088>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_6087!=null][b!=null][res!=null]
                                  [null=l_6086][0=flted_14_6085][0=cl_6088]
                                  [0<=flted_391_120 & flted_391_120<=1]
                                  [0<=flted_391_121 & flted_391_121<=1]
                                  [0<=flted_391_122 & flted_391_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6089,flted_14_6090,l_6091,r_6092,
                                 cl_6093: b::node<v_6089,flted_14_6090,l_6091,r_6092>@M[Orig][] * 
                                 res::rb1<cl_6093>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_6091!=null][b!=null][res!=null]
                                  [null=r_6092][0=flted_14_6090][0=cl_6093]
                                  [0<=flted_391_120 & flted_391_120<=1]
                                  [0<=flted_391_121 & flted_391_121<=1]
                                  [0<=flted_391_122 & flted_391_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6094,flted_14_6095,l_6096,r_6097,
                                 cl_6098: b::node<v_6094,flted_14_6095,l_6096,r_6097>@M[Orig][] * 
                                 res::rb1<cl_6098>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_6096!=null][b!=null][r_6097!=null]
                                  [res!=null][0=cl_6098][0=flted_14_6095]
                                  [0<=flted_391_120 & flted_391_120<=1]
                                  [0<=flted_391_121 & flted_391_121<=1]
                                  [0<=flted_391_122 & flted_391_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6099,flted_14_6100,l_6101,r_6102,
                                 v_6103,flted_13_6104,l_6105,r_6106,
                                 cl_6107: b::node<v_6099,flted_14_6100,l_6101,r_6102>@M[Orig][] * 
                                 r_6102::node<v_6103,flted_13_6104,l_6105,r_6106>@M[Orig][] * 
                                 res::rb1<cl_6107>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_6102!=null][b!=null][res!=null]
                                  [null=l_6101][1=flted_13_6104][0=cl_6107]
                                  [0=flted_14_6100]
                                  [0<=flted_391_120 & flted_391_120<=1]
                                  [0<=flted_391_121 & flted_391_121<=1]
                                  [0<=flted_391_122 & flted_391_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6108,flted_14_6109,l_6110,r_6111,
                                 v_6112,flted_13_6113,l_6114,r_6115,
                                 cl_6116: b::node<v_6108,flted_14_6109,l_6110,r_6111>@M[Orig][] * 
                                 r_6111::node<v_6112,flted_13_6113,l_6114,r_6115>@M[Orig][] * 
                                 res::rb1<cl_6116>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([b!=null][r_6111!=null][l_6110!=null]
                                  [res!=null][0=flted_14_6109][0=cl_6116]
                                  [1=flted_13_6113]
                                  [0<=flted_391_120 & flted_391_120<=1]
                                  [0<=flted_391_121 & flted_391_121<=1]
                                  [0<=flted_391_122 & flted_391_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6117,flted_14_6118,l_6119,r_6120,
                                 cl_6121: b::node<v_6117,flted_14_6118,l_6119,r_6120>@M[Orig][] * 
                                 res::rb1<cl_6121>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([b!=null][l_6119!=null][res!=null]
                                  [0=flted_14_6118][0=cl_6121]
                                  [0<=flted_391_120 & flted_391_120<=1]
                                  [0<=flted_391_121 & flted_391_121<=1]
                                  [0<=flted_391_122 & flted_391_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_2r$node~node~node SUCCESS

Checking procedure del_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_325_162,flted_325_163,
                    flted_325_164: a::rb1<flted_325_164>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_325_163>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_325_162>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_325_164][0=flted_325_163][0=flted_325_162]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_325_164>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_325_163>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_325_162>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_325_164][0=flted_325_163][0=flted_325_162]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(cl_6251: res::rb1<cl_6251>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6251]
                               [0<=flted_325_162 & flted_325_162<=1]
                               [0<=flted_325_163 & flted_325_163<=1]
                               [0<=flted_325_164 & flted_325_164<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_344_149,flted_344_150,
                    flted_344_151: a::rb1<flted_344_151>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_344_150>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_344_149>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_344_151][0=flted_344_150][0=flted_344_149]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_344_151>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_344_150>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_344_149>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_344_151][0=flted_344_150][0=flted_344_149]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(cl_6378: res::rb1<cl_6378>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6378]
                               [0<=flted_344_149 & flted_344_149<=1]
                               [0<=flted_344_150 & flted_344_150<=1]
                               [0<=flted_344_151 & flted_344_151<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_289_188,flted_289_189,
                    flted_289_190: a::rb1<flted_289_190>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_289_189>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_289_188>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_289_190][0=flted_289_189][0=flted_289_188]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_289_190>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_289_189>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_289_188>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_289_190][0=flted_289_189][0=flted_289_188]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(cl_6516: res::rb1<cl_6516>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6516]
                               [0<=flted_289_188 & flted_289_188<=1]
                               [0<=flted_289_189 & flted_289_189<=1]
                               [0<=flted_289_190 & flted_289_190<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_306_175,flted_306_176,
                    flted_306_177: a::rb1<flted_306_177>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_306_176>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_306_175>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_306_177][0=flted_306_176][0=flted_306_175]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_306_177>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_306_176>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_306_175>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_306_177][0=flted_306_176][0=flted_306_175]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(cl_6643: res::rb1<cl_6643>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6643]
                               [0<=flted_306_175 & flted_306_175<=1]
                               [0<=flted_306_176 & flted_306_176<=1]
                               [0<=flted_306_177 & flted_306_177<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase 
                    EXISTS(flted_234_240,flted_234_241,flted_234_242,
                    flted_234_243: a::rb1<flted_234_243>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_234_242>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_234_241>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_234_240>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_234_243][0=flted_234_242][0=flted_234_241]
                     [0=flted_234_240][0=color]))&
                    {FLOW,(20,21)=__norm})
                    or EXISTS(flted_235_244,flted_235_245,flted_235_246,
                       flted_235_247: a::rb1<flted_235_247>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       b::rb1<flted_235_246>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       c::rb1<flted_235_245>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       d::rb1<flted_235_244>@M[Orig][LHSCase]@ rem br[{701,699}]&
                       (
                       ([0=flted_235_247][0=flted_235_246][0=flted_235_245]
                        [0=flted_235_244][1=color]))&
                       {FLOW,(20,21)=__norm})
                    
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase 
                  a::rb1<flted_234_243>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_234_242>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_234_241>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_234_240>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_234_243][0=flted_234_242][0=flted_234_241]
                   [0=flted_234_240][0=color]))&
                  {FLOW,(20,21)=__norm}
                  or a::rb1<flted_235_247>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     b::rb1<flted_235_246>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     c::rb1<flted_235_245>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     d::rb1<flted_235_244>@M[Orig][LHSCase]@ rem br[{701,699}]&
                     (
                     ([0=flted_235_247][0=flted_235_246][0=flted_235_245]
                      [0=flted_235_244][1=color]))&
                     {FLOW,(20,21)=__norm}
                  
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              
                              EXISTS(cl_6890: res::rb1<cl_6890>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6890][0=color]
                               [0<=flted_234_243 & flted_234_243<=1 & 
                                 0<=flted_234_242 & flted_234_242<=1 & 
                                 0<=flted_234_241 & flted_234_241<=1 & 
                                 0<=flted_234_240 & flted_234_240<=1 | 
                                 0<=flted_235_247 & flted_235_247<=1 & 
                                 0<=flted_235_246 & flted_235_246<=1 & 
                                 0<=flted_235_245 & flted_235_245<=1 & 
                                 0<=flted_235_244 & flted_235_244<=1]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_6891: res::rb1<cl_6891>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][1=cl_6891][1=color]
                                  [0<=flted_234_243 & flted_234_243<=1 & 
                                    0<=flted_234_242 & flted_234_242<=1 & 
                                    0<=flted_234_241 & flted_234_241<=1 & 
                                    0<=flted_234_240 & flted_234_240<=1 | 
                                    0<=flted_235_247 & flted_235_247<=1 & 
                                    0<=flted_235_246 & flted_235_246<=1 & 
                                    0<=flted_235_245 & flted_235_245<=1 & 
                                    0<=flted_235_244 & flted_235_244<=1]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5$node~node~node~node~int SUCCESS

Checking procedure del_5r$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase 
                    EXISTS(flted_264_207,flted_264_208,flted_264_209,
                    flted_264_210: a::rb1<flted_264_210>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_264_209>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_264_208>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_264_207>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_264_210][0=flted_264_209][0=flted_264_208]
                     [0=flted_264_207][0=color]))&
                    {FLOW,(20,21)=__norm})
                    or EXISTS(flted_265_211,flted_265_212,flted_265_213,
                       flted_265_214: a::rb1<flted_265_214>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       b::rb1<flted_265_213>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       c::rb1<flted_265_212>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       d::rb1<flted_265_211>@M[Orig][LHSCase]@ rem br[{701,699}]&
                       (
                       ([0=flted_265_214][0=flted_265_213][0=flted_265_212]
                        [0=flted_265_211][1=color]))&
                       {FLOW,(20,21)=__norm})
                    
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase 
                  a::rb1<flted_264_210>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_264_209>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_264_208>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_264_207>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_264_210][0=flted_264_209][0=flted_264_208]
                   [0=flted_264_207][0=color]))&
                  {FLOW,(20,21)=__norm}
                  or a::rb1<flted_265_214>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     b::rb1<flted_265_213>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     c::rb1<flted_265_212>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     d::rb1<flted_265_211>@M[Orig][LHSCase]@ rem br[{701,699}]&
                     (
                     ([0=flted_265_214][0=flted_265_213][0=flted_265_212]
                      [0=flted_265_211][1=color]))&
                     {FLOW,(20,21)=__norm}
                  
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              
                              EXISTS(cl_7144: res::rb1<cl_7144>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([0=cl_7144][0=color]
                               [0<=flted_264_210 & flted_264_210<=1 & 
                                 0<=flted_264_209 & flted_264_209<=1 & 
                                 0<=flted_264_208 & flted_264_208<=1 & 
                                 0<=flted_264_207 & flted_264_207<=1 | 
                                 0<=flted_265_214 & flted_265_214<=1 & 
                                 0<=flted_265_213 & flted_265_213<=1 & 
                                 0<=flted_265_212 & flted_265_212<=1 & 
                                 0<=flted_265_211 & flted_265_211<=1]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_7145: res::rb1<cl_7145>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][1=cl_7145][1=color]
                                  [0<=flted_264_210 & flted_264_210<=1 & 
                                    0<=flted_264_209 & flted_264_209<=1 & 
                                    0<=flted_264_208 & flted_264_208<=1 & 
                                    0<=flted_264_207 & flted_264_207<=1 | 
                                    0<=flted_265_214 & flted_265_214<=1 & 
                                    0<=flted_265_213 & flted_265_213<=1 & 
                                    0<=flted_265_212 & flted_265_212<=1 & 
                                    0<=flted_265_211 & flted_265_211<=1]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_5r$node~node~node~node~int SUCCESS

Checking procedure del_6$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_15; 
                    Anon_16](ex)
                                EXISTS(flted_165_286,
                                flted_165_287: a::rb1<flted_165_287>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                                b::rb1<Anon_15>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                c::rb1<flted_165_286>@M[Orig][LHSCase]@ rem br[{700}]&
                                (
                                ([0=flted_165_287][flted_165_286=1][0=color]
                                 [Anon_15<=1 & 0<=Anon_15][null!=c]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_166_288,
                                   flted_166_289: a::rb1<flted_166_289>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                                   b::rb1<Anon_16>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                   c::rb1<flted_166_288>@M[Orig][LHSCase]@ rem br[{700}]&
                                   (
                                   ([0=flted_166_289][flted_166_288=1]
                                    [1=color][Anon_16<=1 & 0<=Anon_16]
                                    [null!=c]))&
                                   {FLOW,(20,21)=__norm})
                                
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15; 
                  Anon_16](ex)
                              a::rb1<flted_165_287>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                              b::rb1<Anon_15>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                              c::rb1<flted_165_286>@M[Orig][LHSCase]@ rem br[{700}]&
                              (
                              ([c!=null][0=flted_165_287][1=flted_165_286]
                               [0=color][Anon_15<=1 & 0<=Anon_15]))&
                              {FLOW,(20,21)=__norm}
                              or a::rb1<flted_166_289>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                                 b::rb1<Anon_16>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                 c::rb1<flted_166_288>@M[Orig][LHSCase]@ rem br[{700}]&
                                 (
                                 ([c!=null][0=flted_166_289][1=flted_166_288]
                                  [1=color][Anon_16<=1 & 0<=Anon_16]))&
                                 {FLOW,(20,21)=__norm}
                              
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              
                              EXISTS(cl_7810: res::rb1<cl_7810>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([c!=null][res!=null][0=color][0=cl_7810]
                               [Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_165_287 & flted_165_287<=1 & 
                                 0<=Anon_15 & Anon_15<=1 & 
                                 0<=flted_165_286 & flted_165_286<=1 | 
                                 0<=flted_166_289 & flted_166_289<=1 & 
                                 0<=Anon_16 & Anon_16<=1 & 
                                 0<=flted_166_288 & flted_166_288<=1)]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_7811: res::rb1<cl_7811>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([c!=null][res!=null][1=color][1=cl_7811]
                                  [Anon_16<=1 & 0<=Anon_16 & 
                                    (0<=flted_165_287 & flted_165_287<=1 & 
                                    0<=Anon_15 & Anon_15<=1 & 
                                    0<=flted_165_286 & flted_165_286<=1 | 
                                    0<=flted_166_289 & flted_166_289<=1 & 
                                    0<=Anon_16 & Anon_16<=1 & 
                                    0<=flted_166_288 & flted_166_288<=1)]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6$node~node~node~int SUCCESS

Checking procedure del_6r$node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_19; 
                    Anon_20](ex)
                                EXISTS(flted_201_269,
                                flted_201_270: a::rb1<flted_201_270>@M[Orig][LHSCase]@ rem br[{700}] * 
                                b::rb1<Anon_19>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                c::rb1<flted_201_269>@M[Orig][LHSCase]@ rem br[{701,699}]&
                                (
                                ([flted_201_270=1][0=flted_201_269][0=color]
                                 [null!=a][Anon_19<=1 & 0<=Anon_19]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_202_271,
                                   flted_202_272: a::rb1<flted_202_272>@M[Orig][LHSCase]@ rem br[{700}] * 
                                   b::rb1<Anon_20>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                   c::rb1<flted_202_271>@M[Orig][LHSCase]@ rem br[{701,699}]&
                                   (
                                   ([flted_202_272=1][0=flted_202_271]
                                    [1=color][null!=a]
                                    [Anon_20<=1 & 0<=Anon_20]))&
                                   {FLOW,(20,21)=__norm})
                                
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; 
                  Anon_20](ex)
                              a::rb1<flted_201_270>@M[Orig][LHSCase]@ rem br[{700}] * 
                              b::rb1<Anon_19>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                              c::rb1<flted_201_269>@M[Orig][LHSCase]@ rem br[{701,699}]&
                              (
                              ([a!=null][1=flted_201_270][0=flted_201_269]
                               [0=color][Anon_19<=1 & 0<=Anon_19]))&
                              {FLOW,(20,21)=__norm}
                              or a::rb1<flted_202_272>@M[Orig][LHSCase]@ rem br[{700}] * 
                                 b::rb1<Anon_20>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                 c::rb1<flted_202_271>@M[Orig][LHSCase]@ rem br[{701,699}]&
                                 (
                                 ([a!=null][1=flted_202_272][0=flted_202_271]
                                  [1=color][Anon_20<=1 & 0<=Anon_20]))&
                                 {FLOW,(20,21)=__norm}
                              
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              
                              EXISTS(cl_8488: res::rb1<cl_8488>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([a!=null][res!=null][0=color][0=cl_8488]
                               [Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_201_270 & flted_201_270<=1 & 
                                 0<=Anon_19 & Anon_19<=1 & 
                                 0<=flted_201_269 & flted_201_269<=1 | 
                                 0<=flted_202_272 & flted_202_272<=1 & 
                                 0<=Anon_20 & Anon_20<=1 & 
                                 0<=flted_202_271 & flted_202_271<=1)]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_8489: res::rb1<cl_8489>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([a!=null][res!=null][1=color][1=cl_8489]
                                  [Anon_20<=1 & 0<=Anon_20 & 
                                    (0<=flted_201_270 & flted_201_270<=1 & 
                                    0<=Anon_19 & Anon_19<=1 & 
                                    0<=flted_201_269 & flted_201_269<=1 | 
                                    0<=flted_202_272 & flted_202_272<=1 & 
                                    0<=Anon_20 & Anon_20<=1 & 
                                    0<=flted_202_271 & flted_202_271<=1)]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6r$node~node~node~int SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(res)
!!! POST:  res!=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[Anon_21](ex)x::rb1<Anon_21>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                    (([Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 112::
                                EXISTS(Anon_22: res::rb1<Anon_22>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([INS(res)][Anon_22<=1 & 0<=Anon_22]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_21](ex)x::rb1<Anon_21>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                  (([Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 112::
                              EXISTS(Anon_9112: res::rb1<Anon_9112>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0<=Anon_9112 & Anon_9112<=1]
                               [Anon_21<=1 & 0<=Anon_21]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (res!=null) --> INS(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure is_black$node... 
!!! REL :  IB1(cl,res)
!!! POST:  !(res) & 1=cl
!!! PRE :  true
!!! REL :  IB2(cl,res)
!!! POST:  res & 0=cl
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [IB1,IB2,x]
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             cl=1 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 21::
                                                          EXISTS(cl_300: 
                                                          x::rb1<cl_300>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                          (
                                                          ([cl=cl_300 & 
                                                             0<=cl_300 & 
                                                             cl_300<=1 & 
                                                             IB1(cl,res)]
                                                           ))&
                                                          {FLOW,(20,21)=__norm}))
                             ;
                             cl!=1 -> ((None,[]),EBase true&MayLoop&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 22::
                                                           EXISTS(cl_299: 
                                                           x::rb1<cl_299>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                           (
                                                           ([cl=cl_299 & 
                                                              0<=cl_299 & 
                                                              cl_299<=1 & 
                                                              IB2(cl,res)]
                                                            ))&
                                                           {FLOW,(20,21)=__norm}))
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           cl=1 -> ((None,[]),EBase true&(([MayLoop]))&
                                                    {FLOW,(1,23)=__flow}
                                                      EAssume 21::
                                                        EXISTS(cl_9272: 
                                                        x::rb1<cl_9272>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                        (
                                                        ([cl=1 & 
                                                           cl=cl_9272 & 
                                                           cl_9272<=1 & 0<=cl]
                                                         [!(res)]))&
                                                        {FLOW,(20,21)=__norm}))
                           ;
                           cl!=1 -> ((None,[]),EBase true&(([MayLoop]))&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 22::
                                                         EXISTS(cl_9273: 
                                                         x::rb1<cl_9273>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                         (
                                                         ([cl=0 & 
                                                            cl=cl_9273 & 
                                                            0<=cl & cl<=1 & 
                                                            cl!=1]
                                                          [res]))&
                                                         {FLOW,(20,21)=__norm}))
                           
                           })
!!! NEW RELS:[ (cl=1 & res<=0) --> IB1(cl,res),
 (cl=0 & 1<=res) --> IB2(cl,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
!!! REL :  IR1(cl,res)
!!! POST:  !(res) & 0=cl
!!! PRE :  true
!!! REL :  IR2(cl,res)
!!! POST:  res & 1=cl
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [IR1,IR2]
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             cl=0 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 15::
                                                          EXISTS(cl_306: 
                                                          x::rb1<cl_306>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                          (
                                                          ([cl=cl_306 & 
                                                             0<=cl_306 & 
                                                             cl_306<=1 & 
                                                             IR1(cl,res)]
                                                           ))&
                                                          {FLOW,(20,21)=__norm}))
                             ;
                             cl!=0 -> ((None,[]),EBase true&MayLoop&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 16::
                                                           EXISTS(cl_305: 
                                                           x::rb1<cl_305>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                           (
                                                           ([cl=cl_305 & 
                                                              0<=cl_305 & 
                                                              cl_305<=1 & 
                                                              IR2(cl,res)]
                                                            ))&
                                                           {FLOW,(20,21)=__norm}))
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           cl=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                    {FLOW,(1,23)=__flow}
                                                      EAssume 15::
                                                        EXISTS(cl_9433: 
                                                        x::rb1<cl_9433>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                        (
                                                        ([cl=0 & 
                                                           cl=cl_9433 & 
                                                           cl_9433<=1 & 0<=cl]
                                                         [!(res)]))&
                                                        {FLOW,(20,21)=__norm}))
                           ;
                           cl!=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 16::
                                                         EXISTS(cl_9434: 
                                                         x::rb1<cl_9434>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                                         (
                                                         ([cl=1 & 
                                                            cl=cl_9434 & 
                                                            0<=cl & cl<=1 & 
                                                            cl!=0]
                                                          [res]))&
                                                         {FLOW,(20,21)=__norm}))
                           
                           })
!!! NEW RELS:[ (cl=0 & res<=0) --> IR1(cl,res),
 (cl=1 & 1<=res) --> IR2(cl,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_red$node SUCCESS

Checking procedure remove_min$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! REL :  RMVM1(cl2,cl)
!!! POST:  0=cl2 & 1=cl
!!! PRE :  true
!!! REL :  RMVM2(cl3,cl)
!!! POST:  cl>=0 & 1>=cl & 0=cl3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,RMVM1,RMVM2]
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::ref [x]
                                
                                EXISTS(cl2: x'::rb1<cl2>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([1=cl & 0<=cl2 & cl2<=1 & RMVM1(cl2,cl)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl3: x'::rb1<cl3>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                   (([0<=cl3 & cl3<=1 & RMVM2(cl3,cl)]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 66::ref [x]
                              
                              EXISTS(cl2_9958: x'::rb1<cl2_9958>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([cl=1 & 0<=cl & cl<=1]
                               [0=cl2_9958 & 0<=cl2_9958 & cl2_9958<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl3_9959: x'::rb1<cl3_9959>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([0=cl3_9959 & 0<=cl3_9959 & cl3_9959<=1]
                                  [cl<=1 & 0<=cl]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (cl2=0 & cl=1) --> RMVM1(cl2,cl),
 (cl=1 & cl2=0) --> RMVM1(cl2,cl),
 (cl3=0 & cl=1) --> RMVM2(cl3,cl),
 (cl=1 & cl3=0) --> RMVM2(cl3,cl),
 (cl3=0 & cl=0) --> RMVM2(cl3,cl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure remove_min$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_25_359,flted_25_360,
                    flted_25_361: a::rb1<flted_25_361>@M[Orig][LHSCase]@ rem br[{700}] * 
                    b::rb1<flted_25_360>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_25_359>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([flted_25_361=1][0=flted_25_360][0=flted_25_359]
                     [null!=a]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_25_361>@M[Orig][LHSCase]@ rem br[{700}] * 
                  b::rb1<flted_25_360>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_25_359>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([a!=null][1=flted_25_361][0=flted_25_360][0=flted_25_359]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(cl_10089: res::rb1<cl_10089>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][a!=null][0=cl_10089]
                               [0<=flted_25_359 & flted_25_359<=1]
                               [0<=flted_25_360 & flted_25_360<=1]
                               [0<=flted_25_361 & flted_25_361<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_63_329,flted_63_330,
                    flted_63_331: a::rb1<flted_63_331>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_63_330>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_63_329>@M[Orig][LHSCase]@ rem br[{700}]&(
                    ([0=flted_63_331][0=flted_63_330][flted_63_329=1]
                     [null!=c]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_63_331>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_63_330>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_63_329>@M[Orig][LHSCase]@ rem br[{700}]&(
                  ([c!=null][0=flted_63_331][0=flted_63_330][1=flted_63_329]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(cl_10216: res::rb1<cl_10216>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][c!=null][0=cl_10216]
                               [0<=flted_63_329 & flted_63_329<=1]
                               [0<=flted_63_330 & flted_63_330<=1]
                               [0<=flted_63_331 & flted_63_331<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 2971 invocations 
316 false contexts at: ( (509,3)  (509,10)  (506,4)  (506,11)  (501,22)  (501,29)  (500,26)  (500,71)  (500,56)  (500,42)  (500,34)  (500,22)  (500,22)  (495,26)  (495,33)  (494,30)  (494,100)  (494,85)  (494,65)  (494,46)  (494,38)  (494,26)  (494,26)  (490,28)  (490,35)  (489,32)  (489,62)  (489,48)  (489,40)  (489,28)  (489,28)  (485,28)  (485,35)  (484,32)  (484,62)  (484,48)  (484,40)  (484,28)  (484,28)  (482,39)  (482,28)  (482,28)  (482,24)  (481,37)  (481,26)  (481,22)  (479,33)  (479,22)  (479,18)  (475,20)  (475,27)  (472,22)  (472,29)  (471,26)  (471,56)  (471,42)  (471,34)  (471,22)  (471,22)  (469,22)  (469,22)  (469,18)  (467,27)  (467,18)  (467,14)  (465,25)  (465,14)  (465,10)  (463,10)  (463,26)  (463,23)  (116,3)  (116,10)  (113,2)  (113,9)  (118,3)  (118,10)  (149,3)  (149,10)  (147,3)  (147,10)  (144,2)  (144,9)  (747,14)  (744,16)  (740,24)  (737,28)  (737,35)  (736,32)  (736,71)  (736,57)  (736,49)  (736,28)  (736,28)  (732,28)  (732,35)  (731,44)  (731,28)  (730,43)  (730,28)  (730,28)  (728,37)  (728,28)  (728,24)  (723,24)  (723,31)  (722,28)  (722,85)  (722,65)  (722,46)  (722,38)  (722,24)  (722,24)  (718,24)  (718,31)  (717,40)  (717,24)  (716,39)  (716,24)  (716,24)  (714,33)  (714,24)  (714,20)  (701,12)  (698,16)  (694,24)  (690,30)  (690,37)  (689,34)  (689,95)  (689,75)  (689,56)  (689,43)  (689,30)  (689,30)  (685,30)  (685,37)  (684,46)  (684,30)  (683,45)  (683,30)  (683,30)  (681,39)  (681,30)  (681,26)  (674,26)  (674,33)  (673,30)  (673,73)  (673,59)  (673,46)  (673,26)  (673,26)  (669,26)  (669,33)  (668,42)  (668,26)  (667,41)  (667,26)  (667,26)  (665,35)  (665,26)  (665,22)  (610,14)  (631,30)  (631,75)  (631,60)  (631,46)  (631,38)  (631,26)  (629,32)  (629,102)  (629,87)  (629,67)  (629,48)  (629,40)  (629,28)  (626,36)  (626,66)  (626,52)  (626,44)  (626,32)  (624,36)  (624,66)  (624,52)  (624,44)  (624,32)  (623,45)  (623,34)  (623,34)  (623,30)  (621,41)  (621,30)  (621,26)  (620,39)  (620,28)  (620,24)  (616,30)  (616,60)  (616,46)  (616,38)  (616,26)  (615,28)  (615,28)  (615,24)  (613,33)  (613,24)  (613,20)  (612,33)  (612,22)  (612,18)  (610,18)  (610,34)  (610,31)  (583,14)  (602,34)  (602,79)  (602,70)  (602,56)  (602,43)  (602,30)  (600,32)  (600,102)  (600,93)  (600,73)  (600,54)  (600,41)  (600,28)  (598,34)  (598,70)  (598,56)  (598,43)  (598,30)  (596,34)  (596,70)  (596,56)  (596,43)  (596,30)  (595,43)  (595,32)  (595,32)  (595,28)  (594,41)  (594,30)  (594,26)  (593,39)  (593,28)  (593,24)  (589,30)  (589,66)  (589,52)  (589,39)  (589,26)  (588,28)  (588,28)  (588,24)  (586,33)  (586,24)  (586,20)  (585,33)  (585,22)  (585,18)  (583,18)  (583,35)  (583,32)  (550,14)  (570,32)  (570,77)  (570,68)  (570,54)  (570,41)  (570,28)  (568,34)  (568,104)  (568,95)  (568,75)  (568,56)  (568,43)  (568,30)  (566,36)  (566,72)  (566,58)  (566,45)  (566,32)  (564,36)  (564,72)  (564,58)  (564,45)  (564,32)  (563,45)  (563,34)  (563,34)  (563,30)  (562,43)  (562,32)  (562,28)  (561,41)  (561,30)  (561,26)  (557,32)  (557,68)  (557,54)  (557,41)  (557,28)  (556,30)  (556,30)  (556,26)  (554,35)  (554,26)  (554,22)  (552,33)  (552,22)  (552,18)  (550,18)  (550,35)  (550,32) )

Total verification time: 2.46 second(s)
	Time spent in main process: 1.96 second(s)
	Time spent in child processes: 0.5 second(s)
