
Processing file "rb_m.ss"
Parsing rb_m.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure case_2$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_42_343,flted_42_344,flted_42_345,
                    flted_42_346: a::rb1<flted_42_346>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_42_345>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_42_344>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_42_343>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_42_346][0=flted_42_345][0=flted_42_344]
                     [0=flted_42_343]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_42_346>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_42_345>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_42_344>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_42_343>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_42_346][0=flted_42_345][0=flted_42_344]
                   [0=flted_42_343]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(cl_3123: res::rb1<cl_3123>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_3123]
                               [0<=flted_42_343 & flted_42_343<=1]
                               [0<=flted_42_344 & flted_42_344<=1]
                               [0<=flted_42_345 & flted_42_345<=1]
                               [0<=flted_42_346 & flted_42_346<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_77_313,flted_77_314,flted_77_315,
                    flted_77_316: a::rb1<flted_77_316>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_77_315>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_77_314>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_77_313>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_77_316][0=flted_77_315][0=flted_77_314]
                     [0=flted_77_313]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_77_316>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_77_315>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_77_314>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_77_313>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_77_316][0=flted_77_315][0=flted_77_314]
                   [0=flted_77_313]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(cl_3203: res::rb1<cl_3203>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_3203]
                               [0<=flted_77_313 & flted_77_313<=1]
                               [0<=flted_77_314 & flted_77_314<=1]
                               [0<=flted_77_315 & flted_77_315<=1]
                               [0<=flted_77_316 & flted_77_316<=1]))&
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
              EBase EXISTS(flted_348_136,flted_348_137,
                    flted_348_138: a::rb1<flted_348_138>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_348_137>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_348_136>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_348_138][0=flted_348_137][0=flted_348_136]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_348_138>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_348_137>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_348_136>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_348_138][0=flted_348_137][0=flted_348_136]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][b!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              
                              EXISTS(v_5169,flted_14_5170,l_5171,r_5172,
                              cl_5173: b::node<v_5169,flted_14_5170,l_5171,r_5172>@M[Orig][] * 
                              res::rb1<cl_5173>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][b!=null][null=r_5172][null=l_5171]
                               [0=flted_14_5170][0=cl_5173]
                               [0<=flted_348_136 & flted_348_136<=1]
                               [0<=flted_348_137 & flted_348_137<=1]
                               [0<=flted_348_138 & flted_348_138<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_5174,flted_14_5175,l_5176,r_5177,
                                 cl_5178: b::node<v_5174,flted_14_5175,l_5176,r_5177>@M[Orig][] * 
                                 res::rb1<cl_5178>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_5176!=null][res!=null][b!=null]
                                  [null=r_5177][0=cl_5178][0=flted_14_5175]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5179,flted_14_5180,l_5181,r_5182,
                                 cl_5183: b::node<v_5179,flted_14_5180,l_5181,r_5182>@M[Orig][] * 
                                 res::rb1<cl_5183>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_5182!=null][res!=null][b!=null]
                                  [null=l_5181][0=cl_5183][0=flted_14_5180]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5184,flted_14_5185,l_5186,r_5187,
                                 cl_5188: b::node<v_5184,flted_14_5185,l_5186,r_5187>@M[Orig][] * 
                                 res::rb1<cl_5188>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_5187!=null][b!=null][l_5186!=null]
                                  [res!=null][0=flted_14_5185][0=cl_5188]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
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
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
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
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5207,flted_14_5208,l_5209,r_5210,
                                 cl_5211: b::node<v_5207,flted_14_5208,l_5209,r_5210>@M[Orig][] * 
                                 res::rb1<cl_5211>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][r_5210!=null][b!=null]
                                  [0=flted_14_5208][0=cl_5211]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
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
              EBase EXISTS(flted_375_120,flted_375_121,
                    flted_375_122: a::rb1<flted_375_122>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_375_121>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_375_120>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_375_122][0=flted_375_121][0=flted_375_120]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_375_122>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_375_121>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_375_120>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_375_122][0=flted_375_121][0=flted_375_120]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][b!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 59::
                              
                              EXISTS(v_6079,flted_14_6080,l_6081,r_6082,
                              cl_6083: b::node<v_6079,flted_14_6080,l_6081,r_6082>@M[Orig][] * 
                              res::rb1<cl_6083>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([b!=null][res!=null][null=r_6082][null=l_6081]
                               [0=cl_6083][0=flted_14_6080]
                               [0<=flted_375_120 & flted_375_120<=1]
                               [0<=flted_375_121 & flted_375_121<=1]
                               [0<=flted_375_122 & flted_375_122<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_6084,flted_14_6085,l_6086,r_6087,
                                 cl_6088: b::node<v_6084,flted_14_6085,l_6086,r_6087>@M[Orig][] * 
                                 res::rb1<cl_6088>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([r_6087!=null][b!=null][res!=null]
                                  [null=l_6086][0=flted_14_6085][0=cl_6088]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6089,flted_14_6090,l_6091,r_6092,
                                 cl_6093: b::node<v_6089,flted_14_6090,l_6091,r_6092>@M[Orig][] * 
                                 res::rb1<cl_6093>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_6091!=null][b!=null][res!=null]
                                  [null=r_6092][0=flted_14_6090][0=cl_6093]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6094,flted_14_6095,l_6096,r_6097,
                                 cl_6098: b::node<v_6094,flted_14_6095,l_6096,r_6097>@M[Orig][] * 
                                 res::rb1<cl_6098>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([l_6096!=null][b!=null][r_6097!=null]
                                  [res!=null][0=cl_6098][0=flted_14_6095]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
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
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
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
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6117,flted_14_6118,l_6119,r_6120,
                                 cl_6121: b::node<v_6117,flted_14_6118,l_6119,r_6120>@M[Orig][] * 
                                 res::rb1<cl_6121>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([b!=null][l_6119!=null][res!=null]
                                  [0=flted_14_6118][0=cl_6121]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_2r$node~node~node SUCCESS

Checking procedure del_3$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_312_162,flted_312_163,
                    flted_312_164: a::rb1<flted_312_164>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_312_163>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_312_162>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_312_164][0=flted_312_163][0=flted_312_162]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_312_164>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_312_163>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_312_162>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_312_164][0=flted_312_163][0=flted_312_162]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(cl_6251: res::rb1<cl_6251>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6251]
                               [0<=flted_312_162 & flted_312_162<=1]
                               [0<=flted_312_163 & flted_312_163<=1]
                               [0<=flted_312_164 & flted_312_164<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_330_149,flted_330_150,
                    flted_330_151: a::rb1<flted_330_151>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_330_150>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_330_149>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_330_151][0=flted_330_150][0=flted_330_149]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_330_151>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_330_150>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_330_149>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_330_151][0=flted_330_150][0=flted_330_149]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(cl_6378: res::rb1<cl_6378>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6378]
                               [0<=flted_330_149 & flted_330_149<=1]
                               [0<=flted_330_150 & flted_330_150<=1]
                               [0<=flted_330_151 & flted_330_151<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_278_188,flted_278_189,
                    flted_278_190: a::rb1<flted_278_190>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_278_189>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_278_188>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_278_190][0=flted_278_189][0=flted_278_188]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_278_190>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_278_189>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_278_188>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_278_190][0=flted_278_189][0=flted_278_188]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(cl_6516: res::rb1<cl_6516>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6516]
                               [0<=flted_278_188 & flted_278_188<=1]
                               [0<=flted_278_189 & flted_278_189<=1]
                               [0<=flted_278_190 & flted_278_190<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_294_175,flted_294_176,
                    flted_294_177: a::rb1<flted_294_177>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_294_176>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_294_175>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (([0=flted_294_177][0=flted_294_176][0=flted_294_175]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_294_177>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_294_176>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_294_175>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_294_177][0=flted_294_176][0=flted_294_175]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(cl_6643: res::rb1<cl_6643>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6643]
                               [0<=flted_294_175 & flted_294_175<=1]
                               [0<=flted_294_176 & flted_294_176<=1]
                               [0<=flted_294_177 & flted_294_177<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase 
                    EXISTS(flted_225_240,flted_225_241,flted_225_242,
                    flted_225_243: a::rb1<flted_225_243>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_225_242>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_225_241>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_225_240>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_225_243][0=flted_225_242][0=flted_225_241]
                     [0=flted_225_240][0=color]))&
                    {FLOW,(20,21)=__norm})
                    or EXISTS(flted_226_244,flted_226_245,flted_226_246,
                       flted_226_247: a::rb1<flted_226_247>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       b::rb1<flted_226_246>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       c::rb1<flted_226_245>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       d::rb1<flted_226_244>@M[Orig][LHSCase]@ rem br[{701,699}]&
                       (
                       ([0=flted_226_247][0=flted_226_246][0=flted_226_245]
                        [0=flted_226_244][1=color]))&
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
                  a::rb1<flted_225_243>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_225_242>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_225_241>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_225_240>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_225_243][0=flted_225_242][0=flted_225_241]
                   [0=flted_225_240][0=color]))&
                  {FLOW,(20,21)=__norm}
                  or a::rb1<flted_226_247>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     b::rb1<flted_226_246>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     c::rb1<flted_226_245>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     d::rb1<flted_226_244>@M[Orig][LHSCase]@ rem br[{701,699}]&
                     (
                     ([0=flted_226_247][0=flted_226_246][0=flted_226_245]
                      [0=flted_226_244][1=color]))&
                     {FLOW,(20,21)=__norm}
                  
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              
                              EXISTS(cl_6890: res::rb1<cl_6890>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][0=cl_6890][0=color]
                               [0<=flted_225_243 & flted_225_243<=1 & 
                                 0<=flted_225_242 & flted_225_242<=1 & 
                                 0<=flted_225_241 & flted_225_241<=1 & 
                                 0<=flted_225_240 & flted_225_240<=1 | 
                                 0<=flted_226_247 & flted_226_247<=1 & 
                                 0<=flted_226_246 & flted_226_246<=1 & 
                                 0<=flted_226_245 & flted_226_245<=1 & 
                                 0<=flted_226_244 & flted_226_244<=1]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_6891: res::rb1<cl_6891>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][1=cl_6891][1=color]
                                  [0<=flted_225_243 & flted_225_243<=1 & 
                                    0<=flted_225_242 & flted_225_242<=1 & 
                                    0<=flted_225_241 & flted_225_241<=1 & 
                                    0<=flted_225_240 & flted_225_240<=1 | 
                                    0<=flted_226_247 & flted_226_247<=1 & 
                                    0<=flted_226_246 & flted_226_246<=1 & 
                                    0<=flted_226_245 & flted_226_245<=1 & 
                                    0<=flted_226_244 & flted_226_244<=1]
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
                    EXISTS(flted_254_207,flted_254_208,flted_254_209,
                    flted_254_210: a::rb1<flted_254_210>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_254_209>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_254_208>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    d::rb1<flted_254_207>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([0=flted_254_210][0=flted_254_209][0=flted_254_208]
                     [0=flted_254_207][0=color]))&
                    {FLOW,(20,21)=__norm})
                    or EXISTS(flted_255_211,flted_255_212,flted_255_213,
                       flted_255_214: a::rb1<flted_255_214>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       b::rb1<flted_255_213>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       c::rb1<flted_255_212>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                       d::rb1<flted_255_211>@M[Orig][LHSCase]@ rem br[{701,699}]&
                       (
                       ([0=flted_255_214][0=flted_255_213][0=flted_255_212]
                        [0=flted_255_211][1=color]))&
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
                  a::rb1<flted_254_210>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_254_209>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_254_208>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  d::rb1<flted_254_207>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([0=flted_254_210][0=flted_254_209][0=flted_254_208]
                   [0=flted_254_207][0=color]))&
                  {FLOW,(20,21)=__norm}
                  or a::rb1<flted_255_214>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     b::rb1<flted_255_213>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     c::rb1<flted_255_212>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                     d::rb1<flted_255_211>@M[Orig][LHSCase]@ rem br[{701,699}]&
                     (
                     ([0=flted_255_214][0=flted_255_213][0=flted_255_212]
                      [0=flted_255_211][1=color]))&
                     {FLOW,(20,21)=__norm}
                  
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              
                              EXISTS(cl_7144: res::rb1<cl_7144>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([0=cl_7144][0=color]
                               [0<=flted_254_210 & flted_254_210<=1 & 
                                 0<=flted_254_209 & flted_254_209<=1 & 
                                 0<=flted_254_208 & flted_254_208<=1 & 
                                 0<=flted_254_207 & flted_254_207<=1 | 
                                 0<=flted_255_214 & flted_255_214<=1 & 
                                 0<=flted_255_213 & flted_255_213<=1 & 
                                 0<=flted_255_212 & flted_255_212<=1 & 
                                 0<=flted_255_211 & flted_255_211<=1]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_7145: res::rb1<cl_7145>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([res!=null][1=cl_7145][1=color]
                                  [0<=flted_254_210 & flted_254_210<=1 & 
                                    0<=flted_254_209 & flted_254_209<=1 & 
                                    0<=flted_254_208 & flted_254_208<=1 & 
                                    0<=flted_254_207 & flted_254_207<=1 | 
                                    0<=flted_255_214 & flted_255_214<=1 & 
                                    0<=flted_255_213 & flted_255_213<=1 & 
                                    0<=flted_255_212 & flted_255_212<=1 & 
                                    0<=flted_255_211 & flted_255_211<=1]
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
                                EXISTS(flted_158_286,
                                flted_158_287: a::rb1<flted_158_287>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                                b::rb1<Anon_15>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                c::rb1<flted_158_286>@M[Orig][LHSCase]@ rem br[{700}]&
                                (
                                ([0=flted_158_287][flted_158_286=1][0=color]
                                 [Anon_15<=1 & 0<=Anon_15][null!=c]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_159_288,
                                   flted_159_289: a::rb1<flted_159_289>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                                   b::rb1<Anon_16>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                   c::rb1<flted_159_288>@M[Orig][LHSCase]@ rem br[{700}]&
                                   (
                                   ([0=flted_159_289][flted_159_288=1]
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
                              a::rb1<flted_158_287>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                              b::rb1<Anon_15>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                              c::rb1<flted_158_286>@M[Orig][LHSCase]@ rem br[{700}]&
                              (
                              ([c!=null][0=flted_158_287][1=flted_158_286]
                               [0=color][Anon_15<=1 & 0<=Anon_15]))&
                              {FLOW,(20,21)=__norm}
                              or a::rb1<flted_159_289>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                                 b::rb1<Anon_16>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                 c::rb1<flted_159_288>@M[Orig][LHSCase]@ rem br[{700}]&
                                 (
                                 ([c!=null][0=flted_159_289][1=flted_159_288]
                                  [1=color][Anon_16<=1 & 0<=Anon_16]))&
                                 {FLOW,(20,21)=__norm}
                              
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              
                              EXISTS(cl_7810: res::rb1<cl_7810>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([c!=null][res!=null][0=color][0=cl_7810]
                               [Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_158_287 & flted_158_287<=1 & 
                                 0<=Anon_15 & Anon_15<=1 & 
                                 0<=flted_158_286 & flted_158_286<=1 | 
                                 0<=flted_159_289 & flted_159_289<=1 & 
                                 0<=Anon_16 & Anon_16<=1 & 
                                 0<=flted_159_288 & flted_159_288<=1)]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_7811: res::rb1<cl_7811>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([c!=null][res!=null][1=color][1=cl_7811]
                                  [Anon_16<=1 & 0<=Anon_16 & 
                                    (0<=flted_158_287 & flted_158_287<=1 & 
                                    0<=Anon_15 & Anon_15<=1 & 
                                    0<=flted_158_286 & flted_158_286<=1 | 
                                    0<=flted_159_289 & flted_159_289<=1 & 
                                    0<=Anon_16 & Anon_16<=1 & 
                                    0<=flted_159_288 & flted_159_288<=1)]
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
                                EXISTS(flted_193_269,
                                flted_193_270: a::rb1<flted_193_270>@M[Orig][LHSCase]@ rem br[{700}] * 
                                b::rb1<Anon_19>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                c::rb1<flted_193_269>@M[Orig][LHSCase]@ rem br[{701,699}]&
                                (
                                ([flted_193_270=1][0=flted_193_269][0=color]
                                 [null!=a][Anon_19<=1 & 0<=Anon_19]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_194_271,
                                   flted_194_272: a::rb1<flted_194_272>@M[Orig][LHSCase]@ rem br[{700}] * 
                                   b::rb1<Anon_20>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                   c::rb1<flted_194_271>@M[Orig][LHSCase]@ rem br[{701,699}]&
                                   (
                                   ([flted_194_272=1][0=flted_194_271]
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
                              a::rb1<flted_193_270>@M[Orig][LHSCase]@ rem br[{700}] * 
                              b::rb1<Anon_19>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                              c::rb1<flted_193_269>@M[Orig][LHSCase]@ rem br[{701,699}]&
                              (
                              ([a!=null][1=flted_193_270][0=flted_193_269]
                               [0=color][Anon_19<=1 & 0<=Anon_19]))&
                              {FLOW,(20,21)=__norm}
                              or a::rb1<flted_194_272>@M[Orig][LHSCase]@ rem br[{700}] * 
                                 b::rb1<Anon_20>@M[Orig][LHSCase]@ rem br[{701,700,699}] * 
                                 c::rb1<flted_194_271>@M[Orig][LHSCase]@ rem br[{701,699}]&
                                 (
                                 ([a!=null][1=flted_194_272][0=flted_194_271]
                                  [1=color][Anon_20<=1 & 0<=Anon_20]))&
                                 {FLOW,(20,21)=__norm}
                              
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              
                              EXISTS(cl_8488: res::rb1<cl_8488>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([a!=null][res!=null][0=color][0=cl_8488]
                               [Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_193_270 & flted_193_270<=1 & 
                                 0<=Anon_19 & Anon_19<=1 & 
                                 0<=flted_193_269 & flted_193_269<=1 | 
                                 0<=flted_194_272 & flted_194_272<=1 & 
                                 0<=Anon_20 & Anon_20<=1 & 
                                 0<=flted_194_271 & flted_194_271<=1)]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_8489: res::rb1<cl_8489>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                 (
                                 ([a!=null][res!=null][1=color][1=cl_8489]
                                  [Anon_20<=1 & 0<=Anon_20 & 
                                    (0<=flted_193_270 & flted_193_270<=1 & 
                                    0<=Anon_19 & Anon_19<=1 & 
                                    0<=flted_193_269 & flted_193_269<=1 | 
                                    0<=flted_194_272 & flted_194_272<=1 & 
                                    0<=Anon_20 & Anon_20<=1 & 
                                    0<=flted_194_271 & flted_194_271<=1)]
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
              EBase EXISTS(flted_24_359,flted_24_360,
                    flted_24_361: a::rb1<flted_24_361>@M[Orig][LHSCase]@ rem br[{700}] * 
                    b::rb1<flted_24_360>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_24_359>@M[Orig][LHSCase]@ rem br[{701,699}]&
                    (
                    ([flted_24_361=1][0=flted_24_360][0=flted_24_359]
                     [null!=a]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_24_361>@M[Orig][LHSCase]@ rem br[{700}] * 
                  b::rb1<flted_24_360>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_24_359>@M[Orig][LHSCase]@ rem br[{701,699}]&(
                  ([a!=null][1=flted_24_361][0=flted_24_360][0=flted_24_359]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(cl_10089: res::rb1<cl_10089>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][a!=null][0=cl_10089]
                               [0<=flted_24_359 & flted_24_359<=1]
                               [0<=flted_24_360 & flted_24_360<=1]
                               [0<=flted_24_361 & flted_24_361<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase EXISTS(flted_60_329,flted_60_330,
                    flted_60_331: a::rb1<flted_60_331>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    b::rb1<flted_60_330>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                    c::rb1<flted_60_329>@M[Orig][LHSCase]@ rem br[{700}]&(
                    ([0=flted_60_331][0=flted_60_330][flted_60_329=1]
                     [null!=c]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_60_331>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  b::rb1<flted_60_330>@M[Orig][LHSCase]@ rem br[{701,699}] * 
                  c::rb1<flted_60_329>@M[Orig][LHSCase]@ rem br[{700}]&(
                  ([c!=null][0=flted_60_331][0=flted_60_330][1=flted_60_329]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(cl_10216: res::rb1<cl_10216>@M[Orig][LHSCase]@ rem br[{701,700,699}]&
                              (
                              ([res!=null][c!=null][0=cl_10216]
                               [0<=flted_60_329 & flted_60_329<=1]
                               [0<=flted_60_330 & flted_60_330<=1]
                               [0<=flted_60_331 & flted_60_331<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 2970 invocations 
316 false contexts at: ( (492,3)  (492,10)  (489,4)  (489,11)  (484,22)  (484,29)  (483,26)  (483,71)  (483,56)  (483,42)  (483,34)  (483,22)  (483,22)  (478,26)  (478,33)  (477,30)  (477,100)  (477,85)  (477,65)  (477,46)  (477,38)  (477,26)  (477,26)  (473,28)  (473,35)  (472,32)  (472,62)  (472,48)  (472,40)  (472,28)  (472,28)  (468,28)  (468,35)  (467,32)  (467,62)  (467,48)  (467,40)  (467,28)  (467,28)  (465,39)  (465,28)  (465,28)  (465,24)  (464,37)  (464,26)  (464,22)  (462,33)  (462,22)  (462,18)  (458,20)  (458,27)  (455,22)  (455,29)  (454,26)  (454,56)  (454,42)  (454,34)  (454,22)  (454,22)  (452,22)  (452,22)  (452,18)  (450,27)  (450,18)  (450,14)  (448,25)  (448,14)  (448,10)  (446,10)  (446,26)  (446,23)  (111,3)  (111,10)  (108,2)  (108,9)  (113,3)  (113,10)  (143,3)  (143,10)  (141,3)  (141,10)  (138,2)  (138,9)  (729,14)  (726,16)  (722,24)  (719,28)  (719,35)  (718,32)  (718,71)  (718,57)  (718,49)  (718,28)  (718,28)  (714,28)  (714,35)  (713,44)  (713,28)  (712,43)  (712,28)  (712,28)  (710,37)  (710,28)  (710,24)  (705,24)  (705,31)  (704,28)  (704,85)  (704,65)  (704,46)  (704,38)  (704,24)  (704,24)  (700,24)  (700,31)  (699,40)  (699,24)  (698,39)  (698,24)  (698,24)  (696,33)  (696,24)  (696,20)  (683,12)  (680,16)  (676,24)  (672,30)  (672,37)  (671,34)  (671,95)  (671,75)  (671,56)  (671,43)  (671,30)  (671,30)  (667,30)  (667,37)  (666,46)  (666,30)  (665,45)  (665,30)  (665,30)  (663,39)  (663,30)  (663,26)  (656,26)  (656,33)  (655,30)  (655,73)  (655,59)  (655,46)  (655,26)  (655,26)  (651,26)  (651,33)  (650,42)  (650,26)  (649,41)  (649,26)  (649,26)  (647,35)  (647,26)  (647,22)  (592,14)  (613,30)  (613,75)  (613,60)  (613,46)  (613,38)  (613,26)  (611,32)  (611,102)  (611,87)  (611,67)  (611,48)  (611,40)  (611,28)  (608,36)  (608,66)  (608,52)  (608,44)  (608,32)  (606,36)  (606,66)  (606,52)  (606,44)  (606,32)  (605,45)  (605,34)  (605,34)  (605,30)  (603,41)  (603,30)  (603,26)  (602,39)  (602,28)  (602,24)  (598,30)  (598,60)  (598,46)  (598,38)  (598,26)  (597,28)  (597,28)  (597,24)  (595,33)  (595,24)  (595,20)  (594,33)  (594,22)  (594,18)  (592,18)  (592,34)  (592,31)  (565,14)  (584,34)  (584,79)  (584,70)  (584,56)  (584,43)  (584,30)  (582,32)  (582,102)  (582,93)  (582,73)  (582,54)  (582,41)  (582,28)  (580,34)  (580,70)  (580,56)  (580,43)  (580,30)  (578,34)  (578,70)  (578,56)  (578,43)  (578,30)  (577,43)  (577,32)  (577,32)  (577,28)  (576,41)  (576,30)  (576,26)  (575,39)  (575,28)  (575,24)  (571,30)  (571,66)  (571,52)  (571,39)  (571,26)  (570,28)  (570,28)  (570,24)  (568,33)  (568,24)  (568,20)  (567,33)  (567,22)  (567,18)  (565,18)  (565,35)  (565,32)  (532,14)  (552,32)  (552,77)  (552,68)  (552,54)  (552,41)  (552,28)  (550,34)  (550,104)  (550,95)  (550,75)  (550,56)  (550,43)  (550,30)  (548,36)  (548,72)  (548,58)  (548,45)  (548,32)  (546,36)  (546,72)  (546,58)  (546,45)  (546,32)  (545,45)  (545,34)  (545,34)  (545,30)  (544,43)  (544,32)  (544,28)  (543,41)  (543,30)  (543,26)  (539,32)  (539,68)  (539,54)  (539,41)  (539,28)  (538,30)  (538,30)  (538,26)  (536,35)  (536,26)  (536,22)  (534,33)  (534,22)  (534,18)  (532,18)  (532,35)  (532,32) )

Total verification time: 2.5 second(s)
	Time spent in main process: 2.01 second(s)
	Time spent in child processes: 0.49 second(s)
