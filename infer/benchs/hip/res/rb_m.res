
Processing file "rb_m.ss"
Parsing rb_m.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure case_2$node~node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [cl]
              EBase EXISTS(flted_42_343,flted_42_344,flted_42_345,
                    flted_42_346: a::rb1<flted_42_346>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_42_345>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_42_344>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    d::rb1<flted_42_343>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (
                    ([0=flted_42_346][0=flted_42_345][0=flted_42_344]
                     [0=flted_42_343]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_42_346>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_42_345>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_42_344>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  d::rb1<flted_42_343>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_42_346][0=flted_42_345][0=flted_42_344]
                   [0=flted_42_343]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(cl_3125: res::rb1<cl_3125>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_3125]
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
!!! OLD SPECS: ((None,[]),EInfer [cl]
              EBase EXISTS(flted_77_313,flted_77_314,flted_77_315,
                    flted_77_316: a::rb1<flted_77_316>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_77_315>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_77_314>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    d::rb1<flted_77_313>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (
                    ([0=flted_77_316][0=flted_77_315][0=flted_77_314]
                     [0=flted_77_313]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 11::
                                res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_77_316>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_77_315>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_77_314>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  d::rb1<flted_77_313>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_77_316][0=flted_77_315][0=flted_77_314]
                   [0=flted_77_313]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 11::
                              EXISTS(cl_3205: res::rb1<cl_3205>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_3205]
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
assert/assume:rb_m.ss:517: 4:  : failed


assert:rb_m.ss:518: 7:  : ok


!!! REL :  DEL1(cl3,cl)
!!! POST:  0=cl & 0=cl3
!!! PRE :  true
!!! REL :  DEL2(cl2,cl)
!!! POST:  0=cl2 & 1=cl
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,DEL1,DEL2]
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 79::ref [x]
                                
                                EXISTS(cl2: x'::rb1<cl2>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([1=cl & 0<=cl2 & cl2<=1 & DEL2(cl2,cl)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl3: x'::rb1<cl3>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (
                                   ([0=cl & 0<=cl3 & cl3<=1 & DEL1(cl3,cl)]))&
                                   {FLOW,(20,21)=__norm})
                                or EXISTS(cl_111: x'::rb1<cl_111>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (([cl=cl_111 & cl_111<=1 & 0<=cl_111]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 79::ref [x]
                              
                              EXISTS(cl3_4328: x'::rb1<cl3_4328>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([0=cl3_4328 & 0<=cl3_4328 & cl3_4328<=1]
                               [cl=0 & 0<=cl & cl<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl2_4329: x'::rb1<cl2_4329>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([cl=1 & 0<=cl & cl<=1]
                                  [0=cl2_4329 & 0<=cl2_4329 & cl2_4329<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(cl_4330: x'::rb1<cl_4330>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (([cl=cl_4330 & cl<=1 & 0<=cl]))&
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
                    flted_348_138: a::rb1<flted_348_138>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_348_137>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_348_136>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (([0=flted_348_138][0=flted_348_137][0=flted_348_136]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_348_138>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_348_137>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_348_136>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_348_138][0=flted_348_137][0=flted_348_136]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][b!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              
                              EXISTS(v_5171,flted_14_5172,l_5173,r_5174,
                              cl_5175: b::node<v_5171,flted_14_5172,l_5173,r_5174>@M[Orig][] * 
                              res::rb1<cl_5175>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][b!=null][null=r_5174][null=l_5173]
                               [0=flted_14_5172][0=cl_5175]
                               [0<=flted_348_136 & flted_348_136<=1]
                               [0<=flted_348_137 & flted_348_137<=1]
                               [0<=flted_348_138 & flted_348_138<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_5176,flted_14_5177,l_5178,r_5179,
                                 cl_5180: b::node<v_5176,flted_14_5177,l_5178,r_5179>@M[Orig][] * 
                                 res::rb1<cl_5180>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([l_5178!=null][res!=null][b!=null]
                                  [null=r_5179][0=cl_5180][0=flted_14_5177]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5181,flted_14_5182,l_5183,r_5184,
                                 cl_5185: b::node<v_5181,flted_14_5182,l_5183,r_5184>@M[Orig][] * 
                                 res::rb1<cl_5185>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([r_5184!=null][res!=null][b!=null]
                                  [null=l_5183][0=cl_5185][0=flted_14_5182]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5186,flted_14_5187,l_5188,r_5189,
                                 cl_5190: b::node<v_5186,flted_14_5187,l_5188,r_5189>@M[Orig][] * 
                                 res::rb1<cl_5190>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([r_5189!=null][b!=null][l_5188!=null]
                                  [res!=null][0=flted_14_5187][0=cl_5190]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5191,flted_14_5192,r_5193,l_5194,
                                 v_5195,flted_13_5196,l_5197,r_5198,
                                 cl_5199: b::node<v_5191,flted_14_5192,l_5194,r_5193>@M[Orig][] * 
                                 l_5194::node<v_5195,flted_13_5196,l_5197,r_5198>@M[Orig][] * 
                                 res::rb1<cl_5199>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([res!=null][b!=null][l_5194!=null]
                                  [null=r_5193][0=flted_14_5192][0=cl_5199]
                                  [1=flted_13_5196]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5200,flted_14_5201,r_5202,l_5203,
                                 v_5204,flted_13_5205,l_5206,r_5207,
                                 cl_5208: b::node<v_5200,flted_14_5201,l_5203,r_5202>@M[Orig][] * 
                                 l_5203::node<v_5204,flted_13_5205,l_5206,r_5207>@M[Orig][] * 
                                 res::rb1<cl_5208>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([l_5203!=null][r_5202!=null][res!=null]
                                  [b!=null][1=flted_13_5205][0=cl_5208]
                                  [0=flted_14_5201]
                                  [0<=flted_348_136 & flted_348_136<=1]
                                  [0<=flted_348_137 & flted_348_137<=1]
                                  [0<=flted_348_138 & flted_348_138<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_5209,flted_14_5210,l_5211,r_5212,
                                 cl_5213: b::node<v_5209,flted_14_5210,l_5211,r_5212>@M[Orig][] * 
                                 res::rb1<cl_5213>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([res!=null][r_5212!=null][b!=null]
                                  [0=flted_14_5210][0=cl_5213]
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
                    flted_375_122: a::rb1<flted_375_122>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_375_121>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_375_120>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (([0=flted_375_122][0=flted_375_121][0=flted_375_120]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_375_122>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_375_121>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_375_120>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_375_122][0=flted_375_121][0=flted_375_120]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][b!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 59::
                              
                              EXISTS(v_6081,flted_14_6082,l_6083,r_6084,
                              cl_6085: b::node<v_6081,flted_14_6082,l_6083,r_6084>@M[Orig][] * 
                              res::rb1<cl_6085>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([b!=null][res!=null][null=r_6084][null=l_6083]
                               [0=cl_6085][0=flted_14_6082]
                               [0<=flted_375_120 & flted_375_120<=1]
                               [0<=flted_375_121 & flted_375_121<=1]
                               [0<=flted_375_122 & flted_375_122<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(v_6086,flted_14_6087,l_6088,r_6089,
                                 cl_6090: b::node<v_6086,flted_14_6087,l_6088,r_6089>@M[Orig][] * 
                                 res::rb1<cl_6090>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([r_6089!=null][b!=null][res!=null]
                                  [null=l_6088][0=flted_14_6087][0=cl_6090]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6091,flted_14_6092,l_6093,r_6094,
                                 cl_6095: b::node<v_6091,flted_14_6092,l_6093,r_6094>@M[Orig][] * 
                                 res::rb1<cl_6095>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([l_6093!=null][b!=null][res!=null]
                                  [null=r_6094][0=flted_14_6092][0=cl_6095]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6096,flted_14_6097,l_6098,r_6099,
                                 cl_6100: b::node<v_6096,flted_14_6097,l_6098,r_6099>@M[Orig][] * 
                                 res::rb1<cl_6100>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([l_6098!=null][b!=null][r_6099!=null]
                                  [res!=null][0=cl_6100][0=flted_14_6097]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6101,flted_14_6102,l_6103,r_6104,
                                 v_6105,flted_13_6106,l_6107,r_6108,
                                 cl_6109: b::node<v_6101,flted_14_6102,l_6103,r_6104>@M[Orig][] * 
                                 r_6104::node<v_6105,flted_13_6106,l_6107,r_6108>@M[Orig][] * 
                                 res::rb1<cl_6109>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([r_6104!=null][b!=null][res!=null]
                                  [null=l_6103][1=flted_13_6106][0=cl_6109]
                                  [0=flted_14_6102]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6110,flted_14_6111,l_6112,r_6113,
                                 v_6114,flted_13_6115,l_6116,r_6117,
                                 cl_6118: b::node<v_6110,flted_14_6111,l_6112,r_6113>@M[Orig][] * 
                                 r_6113::node<v_6114,flted_13_6115,l_6116,r_6117>@M[Orig][] * 
                                 res::rb1<cl_6118>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([b!=null][r_6113!=null][l_6112!=null]
                                  [res!=null][0=flted_14_6111][0=cl_6118]
                                  [1=flted_13_6115]
                                  [0<=flted_375_120 & flted_375_120<=1]
                                  [0<=flted_375_121 & flted_375_121<=1]
                                  [0<=flted_375_122 & flted_375_122<=1]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(v_6119,flted_14_6120,l_6121,r_6122,
                                 cl_6123: b::node<v_6119,flted_14_6120,l_6121,r_6122>@M[Orig][] * 
                                 res::rb1<cl_6123>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([b!=null][l_6121!=null][res!=null]
                                  [0=flted_14_6120][0=cl_6123]
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
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase EXISTS(flted_312_162,flted_312_163,
                    flted_312_164: a::rb1<flted_312_164>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_312_163>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_312_162>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (([0=flted_312_164][0=flted_312_163][0=flted_312_162]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_312_164>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_312_163>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_312_162>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_312_164][0=flted_312_163][0=flted_312_162]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              EXISTS(cl_6257: res::rb1<cl_6257>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_6257]
                               [0<=flted_312_162 & flted_312_162<=1]
                               [0<=flted_312_163 & flted_312_163<=1]
                               [0<=flted_312_164 & flted_312_164<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase EXISTS(flted_330_149,flted_330_150,
                    flted_330_151: a::rb1<flted_330_151>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_330_150>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_330_149>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (([0=flted_330_151][0=flted_330_150][0=flted_330_149]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_330_151>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_330_150>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_330_149>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_330_151][0=flted_330_150][0=flted_330_149]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(cl_6386: res::rb1<cl_6386>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_6386]
                               [0<=flted_330_149 & flted_330_149<=1]
                               [0<=flted_330_150 & flted_330_150<=1]
                               [0<=flted_330_151 & flted_330_151<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase EXISTS(flted_278_188,flted_278_189,
                    flted_278_190: a::rb1<flted_278_190>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_278_189>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_278_188>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (([0=flted_278_190][0=flted_278_189][0=flted_278_188]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_278_190>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_278_189>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_278_188>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_278_190][0=flted_278_189][0=flted_278_188]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(cl_6528: res::rb1<cl_6528>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_6528]
                               [0<=flted_278_188 & flted_278_188<=1]
                               [0<=flted_278_189 & flted_278_189<=1]
                               [0<=flted_278_190 & flted_278_190<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase EXISTS(flted_294_175,flted_294_176,
                    flted_294_177: a::rb1<flted_294_177>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_294_176>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_294_175>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (([0=flted_294_177][0=flted_294_176][0=flted_294_175]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_294_177>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_294_176>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_294_175>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_294_177][0=flted_294_176][0=flted_294_175]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::
                              EXISTS(cl_6657: res::rb1<cl_6657>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_6657]
                               [0<=flted_294_175 & flted_294_175<=1]
                               [0<=flted_294_176 & flted_294_176<=1]
                               [0<=flted_294_177 & flted_294_177<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_5$node~node~node~node~int... 
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase 
                    EXISTS(flted_225_240,flted_225_241,flted_225_242,
                    flted_225_243: a::rb1<flted_225_243>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_225_242>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_225_241>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    d::rb1<flted_225_240>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (
                    ([0=flted_225_243][0=flted_225_242][0=flted_225_241]
                     [0=flted_225_240][0=color]))&
                    {FLOW,(20,21)=__norm})
                    or EXISTS(flted_226_244,flted_226_245,flted_226_246,
                       flted_226_247: a::rb1<flted_226_247>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                       b::rb1<flted_226_246>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                       c::rb1<flted_226_245>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                       d::rb1<flted_226_244>@M[Orig][LHSCase]@ rem br[{705,703}]&
                       (
                       ([0=flted_226_247][0=flted_226_246][0=flted_226_245]
                        [0=flted_226_244][1=color]))&
                       {FLOW,(20,21)=__norm})
                    
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase 
                  a::rb1<flted_225_243>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_225_242>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_225_241>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  d::rb1<flted_225_240>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_225_243][0=flted_225_242][0=flted_225_241]
                   [0=flted_225_240][0=color]))&
                  {FLOW,(20,21)=__norm}
                  or a::rb1<flted_226_247>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                     b::rb1<flted_226_246>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                     c::rb1<flted_226_245>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                     d::rb1<flted_226_244>@M[Orig][LHSCase]@ rem br[{705,703}]&
                     (
                     ([0=flted_226_247][0=flted_226_246][0=flted_226_245]
                      [0=flted_226_244][1=color]))&
                     {FLOW,(20,21)=__norm}
                  
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              
                              EXISTS(cl_6904: res::rb1<cl_6904>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0=cl_6904][0=color]
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
                              or EXISTS(cl_6905: res::rb1<cl_6905>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([res!=null][1=cl_6905][1=color]
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
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase 
                    EXISTS(flted_254_207,flted_254_208,flted_254_209,
                    flted_254_210: a::rb1<flted_254_210>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_254_209>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_254_208>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    d::rb1<flted_254_207>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (
                    ([0=flted_254_210][0=flted_254_209][0=flted_254_208]
                     [0=flted_254_207][0=color]))&
                    {FLOW,(20,21)=__norm})
                    or EXISTS(flted_255_211,flted_255_212,flted_255_213,
                       flted_255_214: a::rb1<flted_255_214>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                       b::rb1<flted_255_213>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                       c::rb1<flted_255_212>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                       d::rb1<flted_255_211>@M[Orig][LHSCase]@ rem br[{705,703}]&
                       (
                       ([0=flted_255_214][0=flted_255_213][0=flted_255_212]
                        [0=flted_255_211][1=color]))&
                       {FLOW,(20,21)=__norm})
                    
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase 
                  a::rb1<flted_254_210>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_254_209>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_254_208>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  d::rb1<flted_254_207>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([0=flted_254_210][0=flted_254_209][0=flted_254_208]
                   [0=flted_254_207][0=color]))&
                  {FLOW,(20,21)=__norm}
                  or a::rb1<flted_255_214>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                     b::rb1<flted_255_213>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                     c::rb1<flted_255_212>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                     d::rb1<flted_255_211>@M[Orig][LHSCase]@ rem br[{705,703}]&
                     (
                     ([0=flted_255_214][0=flted_255_213][0=flted_255_212]
                      [0=flted_255_211][1=color]))&
                     {FLOW,(20,21)=__norm}
                  
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              
                              EXISTS(cl_7158: res::rb1<cl_7158>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([0=cl_7158][0=color]
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
                              or EXISTS(cl_7159: res::rb1<cl_7159>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([res!=null][1=cl_7159][1=color]
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
!!! OLD SPECS: ((None,[]),EInfer [res]
              EBase exists (Expl)(Impl)[Anon_15; 
                    Anon_16](ex)
                                EXISTS(flted_158_286,
                                flted_158_287: a::rb1<flted_158_287>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                                b::rb1<Anon_15>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                                c::rb1<flted_158_286>@M[Orig][LHSCase]@ rem br[{704}]&
                                (
                                ([0=flted_158_287][flted_158_286=1][0=color]
                                 [Anon_15<=1 & 0<=Anon_15][null!=c]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_159_288,
                                   flted_159_289: a::rb1<flted_159_289>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                                   b::rb1<Anon_16>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                                   c::rb1<flted_159_288>@M[Orig][LHSCase]@ rem br[{704}]&
                                   (
                                   ([0=flted_159_289][flted_159_288=1]
                                    [1=color][Anon_16<=1 & 0<=Anon_16]
                                    [null!=c]))&
                                   {FLOW,(20,21)=__norm})
                                
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15; 
                  Anon_16](ex)
                              a::rb1<flted_158_287>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                              b::rb1<Anon_15>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                              c::rb1<flted_158_286>@M[Orig][LHSCase]@ rem br[{704}]&
                              (
                              ([c!=null][0=flted_158_287][1=flted_158_286]
                               [0=color][Anon_15<=1 & 0<=Anon_15]))&
                              {FLOW,(20,21)=__norm}
                              or a::rb1<flted_159_289>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                                 b::rb1<Anon_16>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                                 c::rb1<flted_159_288>@M[Orig][LHSCase]@ rem br[{704}]&
                                 (
                                 ([c!=null][0=flted_159_289][1=flted_159_288]
                                  [1=color][Anon_16<=1 & 0<=Anon_16]))&
                                 {FLOW,(20,21)=__norm}
                              
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::
                              
                              EXISTS(cl_7824: res::rb1<cl_7824>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([c!=null][res!=null][0=color][0=cl_7824]
                               [Anon_15<=1 & 0<=Anon_15 & 
                                 (0<=flted_158_287 & flted_158_287<=1 & 
                                 0<=Anon_15 & Anon_15<=1 & 
                                 0<=flted_158_286 & flted_158_286<=1 | 
                                 0<=flted_159_289 & flted_159_289<=1 & 
                                 0<=Anon_16 & Anon_16<=1 & 
                                 0<=flted_159_288 & flted_159_288<=1)]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_7825: res::rb1<cl_7825>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([c!=null][res!=null][1=color][1=cl_7825]
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
!!! OLD SPECS: ((None,[]),EInfer [a,res]
              EBase exists (Expl)(Impl)[Anon_19; 
                    Anon_20](ex)
                                EXISTS(flted_193_269,
                                flted_193_270: a::rb1<flted_193_270>@M[Orig][LHSCase]@ rem br[{704}] * 
                                b::rb1<Anon_19>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                                c::rb1<flted_193_269>@M[Orig][LHSCase]@ rem br[{705,703}]&
                                (
                                ([flted_193_270=1][0=flted_193_269][0=color]
                                 [null!=a][Anon_19<=1 & 0<=Anon_19]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_194_271,
                                   flted_194_272: a::rb1<flted_194_272>@M[Orig][LHSCase]@ rem br[{704}] * 
                                   b::rb1<Anon_20>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                                   c::rb1<flted_194_271>@M[Orig][LHSCase]@ rem br[{705,703}]&
                                   (
                                   ([flted_194_272=1][0=flted_194_271]
                                    [1=color][null!=a]
                                    [Anon_20<=1 & 0<=Anon_20]))&
                                   {FLOW,(20,21)=__norm})
                                
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::
                                
                                EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([0=color][cl<=1 & 0<=cl]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl: res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (([1=color][cl<=1 & 0<=cl]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19; 
                  Anon_20](ex)
                              a::rb1<flted_193_270>@M[Orig][LHSCase]@ rem br[{704}] * 
                              b::rb1<Anon_19>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                              c::rb1<flted_193_269>@M[Orig][LHSCase]@ rem br[{705,703}]&
                              (
                              ([a!=null][1=flted_193_270][0=flted_193_269]
                               [0=color][Anon_19<=1 & 0<=Anon_19]))&
                              {FLOW,(20,21)=__norm}
                              or a::rb1<flted_194_272>@M[Orig][LHSCase]@ rem br[{704}] * 
                                 b::rb1<Anon_20>@M[Orig][LHSCase]@ rem br[{705,704,703}] * 
                                 c::rb1<flted_194_271>@M[Orig][LHSCase]@ rem br[{705,703}]&
                                 (
                                 ([a!=null][1=flted_194_272][0=flted_194_271]
                                  [1=color][Anon_20<=1 & 0<=Anon_20]))&
                                 {FLOW,(20,21)=__norm}
                              
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::
                              
                              EXISTS(cl_8502: res::rb1<cl_8502>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([a!=null][res!=null][0=color][0=cl_8502]
                               [Anon_19<=1 & 0<=Anon_19 & 
                                 (0<=flted_193_270 & flted_193_270<=1 & 
                                 0<=Anon_19 & Anon_19<=1 & 
                                 0<=flted_193_269 & flted_193_269<=1 | 
                                 0<=flted_194_272 & flted_194_272<=1 & 
                                 0<=Anon_20 & Anon_20<=1 & 
                                 0<=flted_194_271 & flted_194_271<=1)]
                               ))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_8503: res::rb1<cl_8503>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([a!=null][res!=null][1=color][1=cl_8503]
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
              EBase exists (Expl)(Impl)[Anon_21](ex)x::rb1<Anon_21>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                    (([Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 114::
                                EXISTS(Anon_22: res::rb1<Anon_22>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([INS(res)][Anon_22<=1 & 0<=Anon_22]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_21](ex)x::rb1<Anon_21>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                  (([Anon_21<=1 & 0<=Anon_21]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 114::
                              EXISTS(Anon_9126: res::rb1<Anon_9126>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][0<=Anon_9126 & Anon_9126<=1]
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
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             cl=1 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 21::
                                                          EXISTS(cl_300: 
                                                          x::rb1<cl_300>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
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
                                                           x::rb1<cl_299>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                                           (
                                                           ([cl=cl_299 & 
                                                              0<=cl_299 & 
                                                              cl_299<=1 & 
                                                              IB2(cl,res)]
                                                            ))&
                                                           {FLOW,(20,21)=__norm}))
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           cl=1 -> ((None,[]),EBase true&(([MayLoop]))&
                                                    {FLOW,(1,23)=__flow}
                                                      EAssume 21::
                                                        EXISTS(cl_9286: 
                                                        x::rb1<cl_9286>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                                        (
                                                        ([cl=1 & 
                                                           cl=cl_9286 & 
                                                           cl_9286<=1 & 0<=cl]
                                                         [!(res)]))&
                                                        {FLOW,(20,21)=__norm}))
                           ;
                           cl!=1 -> ((None,[]),EBase true&(([MayLoop]))&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 22::
                                                         EXISTS(cl_9287: 
                                                         x::rb1<cl_9287>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                                         (
                                                         ([cl=0 & 
                                                            cl=cl_9287 & 
                                                            0<=cl & cl<=1 & 
                                                            cl!=1]
                                                          [res]))&
                                                         {FLOW,(20,21)=__norm}))
                           
                           })
!!! NEW RELS:[ (cl=1 & res<=0) --> IB1(cl,res),
 (cl=0 & 1<=res) --> IB2(cl,res),
 (cl=0 & 1<=res) --> IB2(cl,res),
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
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             cl=0 -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 15::
                                                          EXISTS(cl_306: 
                                                          x::rb1<cl_306>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
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
                                                           x::rb1<cl_305>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                                           (
                                                           ([cl=cl_305 & 
                                                              0<=cl_305 & 
                                                              cl_305<=1 & 
                                                              IR2(cl,res)]
                                                            ))&
                                                           {FLOW,(20,21)=__norm}))
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           cl=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                    {FLOW,(1,23)=__flow}
                                                      EAssume 15::
                                                        EXISTS(cl_9447: 
                                                        x::rb1<cl_9447>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                                        (
                                                        ([cl=0 & 
                                                           cl=cl_9447 & 
                                                           cl_9447<=1 & 0<=cl]
                                                         [!(res)]))&
                                                        {FLOW,(20,21)=__norm}))
                           ;
                           cl!=0 -> ((None,[]),EBase true&(([MayLoop]))&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 16::
                                                         EXISTS(cl_9448: 
                                                         x::rb1<cl_9448>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                                         (
                                                         ([cl=1 & 
                                                            cl=cl_9448 & 
                                                            0<=cl & cl<=1 & 
                                                            cl!=0]
                                                          [res]))&
                                                         {FLOW,(20,21)=__norm}))
                           
                           })
!!! NEW RELS:[ (cl=0 & res<=0) --> IR1(cl,res),
 (cl=0 & res<=0) --> IR1(cl,res),
 (cl=0 & res<=0) --> IR1(cl,res),
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
              EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                    (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::ref [x]
                                
                                EXISTS(cl2: x'::rb1<cl2>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([1=cl & 0<=cl2 & cl2<=1 & RMVM1(cl2,cl)]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl3: x'::rb1<cl3>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                   (([0<=cl3 & cl3<=1 & RMVM2(cl3,cl)]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl](ex)x::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                  (([0<=cl & cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 66::ref [x]
                              
                              EXISTS(cl2_9972: x'::rb1<cl2_9972>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([cl=1 & 0<=cl & cl<=1]
                               [0=cl2_9972 & 0<=cl2_9972 & cl2_9972<=1]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl3_9973: x'::rb1<cl3_9973>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                 (
                                 ([0=cl3_9973 & 0<=cl3_9973 & cl3_9973<=1]
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
!!! OLD SPECS: ((None,[]),EInfer [cl]
              EBase EXISTS(flted_24_359,flted_24_360,
                    flted_24_361: a::rb1<flted_24_361>@M[Orig][LHSCase]@ rem br[{704}] * 
                    b::rb1<flted_24_360>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_24_359>@M[Orig][LHSCase]@ rem br[{705,703}]&
                    (
                    ([flted_24_361=1][0=flted_24_360][0=flted_24_359]
                     [null!=a]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_24_361>@M[Orig][LHSCase]@ rem br[{704}] * 
                  b::rb1<flted_24_360>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_24_359>@M[Orig][LHSCase]@ rem br[{705,703}]&(
                  ([a!=null][1=flted_24_361][0=flted_24_360][0=flted_24_359]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(cl_10103: res::rb1<cl_10103>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][a!=null][0=cl_10103]
                               [0<=flted_24_359 & flted_24_359<=1]
                               [0<=flted_24_360 & flted_24_360<=1]
                               [0<=flted_24_361 & flted_24_361<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [cl]
              EBase EXISTS(flted_60_329,flted_60_330,
                    flted_60_331: a::rb1<flted_60_331>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    b::rb1<flted_60_330>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                    c::rb1<flted_60_329>@M[Orig][LHSCase]@ rem br[{704}]&(
                    ([0=flted_60_331][0=flted_60_330][flted_60_329=1]
                     [null!=c]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 8::
                                res::rb1<cl>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                                (([cl<=1 & 0<=cl]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase a::rb1<flted_60_331>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  b::rb1<flted_60_330>@M[Orig][LHSCase]@ rem br[{705,703}] * 
                  c::rb1<flted_60_329>@M[Orig][LHSCase]@ rem br[{704}]&(
                  ([c!=null][0=flted_60_331][0=flted_60_330][1=flted_60_329]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 8::
                              EXISTS(cl_10230: res::rb1<cl_10230>@M[Orig][LHSCase]@ rem br[{705,704,703}]&
                              (
                              ([res!=null][c!=null][0=cl_10230]
                               [0<=flted_60_329 & flted_60_329<=1]
                               [0<=flted_60_330 & flted_60_330<=1]
                               [0<=flted_60_331 & flted_60_331<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:

Stop Omega... 3348 invocations 
316 false contexts at: ( (492,3)  (492,10)  (489,4)  (489,11)  (484,22)  (484,29)  (483,26)  (483,71)  (483,56)  (483,42)  (483,34)  (483,22)  (483,22)  (478,26)  (478,33)  (477,30)  (477,100)  (477,85)  (477,65)  (477,46)  (477,38)  (477,26)  (477,26)  (473,28)  (473,35)  (472,32)  (472,62)  (472,48)  (472,40)  (472,28)  (472,28)  (468,28)  (468,35)  (467,32)  (467,62)  (467,48)  (467,40)  (467,28)  (467,28)  (465,39)  (465,28)  (465,28)  (465,24)  (464,37)  (464,26)  (464,22)  (462,33)  (462,22)  (462,18)  (458,20)  (458,27)  (455,22)  (455,29)  (454,26)  (454,56)  (454,42)  (454,34)  (454,22)  (454,22)  (452,22)  (452,22)  (452,18)  (450,27)  (450,18)  (450,14)  (448,25)  (448,14)  (448,10)  (446,10)  (446,26)  (446,23)  (111,3)  (111,10)  (108,2)  (108,9)  (113,3)  (113,10)  (143,3)  (143,10)  (141,3)  (141,10)  (138,2)  (138,9)  (727,14)  (724,16)  (720,24)  (717,28)  (717,35)  (716,32)  (716,71)  (716,57)  (716,49)  (716,28)  (716,28)  (712,28)  (712,35)  (711,44)  (711,28)  (710,43)  (710,28)  (710,28)  (708,37)  (708,28)  (708,24)  (703,24)  (703,31)  (702,28)  (702,85)  (702,65)  (702,46)  (702,38)  (702,24)  (702,24)  (698,24)  (698,31)  (697,40)  (697,24)  (696,39)  (696,24)  (696,24)  (694,33)  (694,24)  (694,20)  (681,12)  (678,16)  (674,24)  (670,30)  (670,37)  (669,34)  (669,95)  (669,75)  (669,56)  (669,43)  (669,30)  (669,30)  (665,30)  (665,37)  (664,46)  (664,30)  (663,45)  (663,30)  (663,30)  (661,39)  (661,30)  (661,26)  (654,26)  (654,33)  (653,30)  (653,73)  (653,59)  (653,46)  (653,26)  (653,26)  (649,26)  (649,33)  (648,42)  (648,26)  (647,41)  (647,26)  (647,26)  (645,35)  (645,26)  (645,22)  (590,14)  (611,30)  (611,75)  (611,60)  (611,46)  (611,38)  (611,26)  (609,32)  (609,102)  (609,87)  (609,67)  (609,48)  (609,40)  (609,28)  (606,36)  (606,66)  (606,52)  (606,44)  (606,32)  (604,36)  (604,66)  (604,52)  (604,44)  (604,32)  (603,45)  (603,34)  (603,34)  (603,30)  (601,41)  (601,30)  (601,26)  (600,39)  (600,28)  (600,24)  (596,30)  (596,60)  (596,46)  (596,38)  (596,26)  (595,28)  (595,28)  (595,24)  (593,33)  (593,24)  (593,20)  (592,33)  (592,22)  (592,18)  (590,18)  (590,34)  (590,31)  (563,14)  (582,34)  (582,79)  (582,70)  (582,56)  (582,43)  (582,30)  (580,32)  (580,102)  (580,93)  (580,73)  (580,54)  (580,41)  (580,28)  (578,34)  (578,70)  (578,56)  (578,43)  (578,30)  (576,34)  (576,70)  (576,56)  (576,43)  (576,30)  (575,43)  (575,32)  (575,32)  (575,28)  (574,41)  (574,30)  (574,26)  (573,39)  (573,28)  (573,24)  (569,30)  (569,66)  (569,52)  (569,39)  (569,26)  (568,28)  (568,28)  (568,24)  (566,33)  (566,24)  (566,20)  (565,33)  (565,22)  (565,18)  (563,18)  (563,35)  (563,32)  (530,14)  (550,32)  (550,77)  (550,68)  (550,54)  (550,41)  (550,28)  (548,34)  (548,104)  (548,95)  (548,75)  (548,56)  (548,43)  (548,30)  (546,36)  (546,72)  (546,58)  (546,45)  (546,32)  (544,36)  (544,72)  (544,58)  (544,45)  (544,32)  (543,45)  (543,34)  (543,34)  (543,30)  (542,43)  (542,32)  (542,28)  (541,41)  (541,30)  (541,26)  (537,32)  (537,68)  (537,54)  (537,41)  (537,28)  (536,30)  (536,30)  (536,26)  (534,35)  (534,26)  (534,22)  (532,33)  (532,22)  (532,18)  (530,18)  (530,35)  (530,32) )

Total verification time: 2.6 second(s)
	Time spent in main process: 2.09 second(s)
	Time spent in child processes: 0.51 second(s)
