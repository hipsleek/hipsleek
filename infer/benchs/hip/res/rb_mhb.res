/usr/local/bin/mona

Processing file "rb_mhb.ss"
Parsing rb_mhb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure case_2$node~node~node~node... 
!!! REL :  ROT2(S5,S1,S2,S3,S4)
!!! POST:  S5=union(S1,S2,{0},S3,S4,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT2]
              EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                    S4](ex)EXISTS(bha_411,bha_412,bha_413,flted_42_407,
                    flted_42_408,flted_42_409,
                    flted_42_410: a::rb1<flted_42_410,bha,S1>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    b::rb1<flted_42_409,bha_411,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    c::rb1<flted_42_408,bha_412,S3>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    d::rb1<flted_42_407,bha_413,S4>@M[Orig][LHSCase]@ rem br[{689,687}]&
                    (
                    ([flted_42_410=0][flted_42_409=0][flted_42_408=0]
                     [flted_42_407=0]
                     [bha=bha_413 & bha=bha_412 & bha=bha_411 & 1<=bha_413]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(flted_43_405,flted_43_406,
                                S5: res::rb1<flted_43_406,flted_43_405,S5>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                (
                                ([flted_43_406=0][-1+flted_43_405=bha]
                                 [ROT2(S5,S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                  S4](ex)a::rb1<flted_42_410,bha,S1>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  b::rb1<flted_42_409,bha_411,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  c::rb1<flted_42_408,bha_412,S3>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  d::rb1<flted_42_407,bha_413,S4>@M[Orig][LHSCase]@ rem br[{689,687}]&
                  (
                  ([bha_412=bha & bha_412=bha_413 & bha_412=bha_411 & 
                     1<=bha_412]
                   [0=flted_42_410][0=flted_42_409][0=flted_42_408]
                   [0=flted_42_407]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              EXISTS(flted_43_3817,flted_43_3818,
                              S5_3819: res::rb1<flted_43_3818,flted_43_3817,S5_3819>@M[Orig][LHSCase]@ rem br[{689,687}]&
                              (
                              ([S5_3819=union(S1,S2,{0},S3,S4,{0},{0})]
                               [-1+flted_43_3817=bha & 1<=bha]
                               [0=flted_43_3818][1<=bha_413]
                               [0<=flted_42_407 & flted_42_407<=1]
                               [1<=bha_412]
                               [0<=flted_42_408 & flted_42_408<=1]
                               [1<=bha_411]
                               [0<=flted_42_409 & flted_42_409<=1]
                               [0<=flted_42_410 & flted_42_410<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_3704:exists(v_3731:exists(S4_3806:exists(S3_3707:exists(S2_3705:exists(S2_3737:exists(S1_3734:v_3731=0 & 
  S4_3806=union(S1_3704,S2_3705,S3_3707,{0},{0}) & S1_3704=union(S1_3734,
  S2_3737,{v_3731}) & S4_3806=S5 & S4=S3_3707 & S3=S2_3705 & S2=S2_3737 & 
  S1=S1_3734)))))))) --> ROT2(S5,S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  ROT2R(S5,S1,S2,S3,S4)
!!! POST:  S5=union(S1,S2,S3,S4,{0},{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT2R]
              EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                    S4](ex)EXISTS(bha_355,bha_356,bha_357,flted_82_351,
                    flted_82_352,flted_82_353,
                    flted_82_354: a::rb1<flted_82_354,bha,S1>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    b::rb1<flted_82_353,bha_355,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    c::rb1<flted_82_352,bha_356,S3>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    d::rb1<flted_82_351,bha_357,S4>@M[Orig][LHSCase]@ rem br[{689,687}]&
                    (
                    ([flted_82_354=0][flted_82_353=0][flted_82_352=0]
                     [flted_82_351=0]
                     [bha=bha_357 & bha=bha_356 & bha=bha_355 & 1<=bha_357]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 10::
                                EXISTS(flted_83_349,flted_83_350,
                                S5: res::rb1<flted_83_350,flted_83_349,S5>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                (
                                ([flted_83_350=0][-1+flted_83_349=bha]
                                 [ROT2R(S5,S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                  S4](ex)a::rb1<flted_82_354,bha,S1>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  b::rb1<flted_82_353,bha_355,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  c::rb1<flted_82_352,bha_356,S3>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  d::rb1<flted_82_351,bha_357,S4>@M[Orig][LHSCase]@ rem br[{689,687}]&
                  (
                  ([bha_356=bha & bha_356=bha_357 & bha_356=bha_355 & 
                     1<=bha_356]
                   [0=flted_82_354][0=flted_82_353][0=flted_82_352]
                   [0=flted_82_351]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 10::
                              EXISTS(flted_83_3942,flted_83_3943,
                              S5_3944: res::rb1<flted_83_3943,flted_83_3942,S5_3944>@M[Orig][LHSCase]@ rem br[{689,687}]&
                              (
                              ([S5_3944=union(S1,S2,S3,S4,{0},{0},{0})]
                               [-1+flted_83_3942=bha & 1<=bha]
                               [0=flted_83_3943][1<=bha_357]
                               [0<=flted_82_351 & flted_82_351<=1]
                               [1<=bha_356]
                               [0<=flted_82_352 & flted_82_352<=1]
                               [1<=bha_355]
                               [0<=flted_82_353 & flted_82_353<=1]
                               [0<=flted_82_354 & flted_82_354<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S3_3843:exists(v_3870:exists(S4_3931:exists(S1_3840:exists(S2_3841:exists(S2_3876:exists(S1_3873:v_3870=0 & 
  S4_3931=union(S1_3840,S2_3841,S3_3843,{0},{0}) & S3_3843=union(S1_3873,
  S2_3876,{v_3870}) & S4_3931=S5 & S1=S1_3840 & S2_3841=S2 & S4=S2_3876 & 
  S3=S1_3873)))))))) --> ROT2R(S5,S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure del_4_1$node~node~node... 
Procedure del_4_1$node~node~node SUCCESS

Checking procedure del_6_1$node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_6_1$node~node~node~int SUCCESS

Checking procedure del_5_1$node~node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_5_1$node~node~node~node~int SUCCESS

Checking procedure is_black_1$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure is_black_1$node SUCCESS

Checking procedure del_2_1$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

( [(568::,0 ); (568::,0 ); (562::,0 ); (562::,0 )]) :rb_mhb.ss:261: 9: Postcondition cannot be derived from context


(Cause of PostCond Failure):rb_mhb.ss:261: 9:  List of Partial Context: [PC(2, 0)]
Failed States:
[
 Label: [(568::,0 ); (568::,0 ); (562::,0 ); (562::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S2_5598=S & S2_5598=S3_5746 & S1_5594=S_5676 & S1_5594=S2_5745 & 
S4_6074=union(S1_5744,S2_5745,S3_5746,{0},{0}) & v_int_275_6075=0 & 
S1_6084=S4_6074 & S1_5744=S1 & S2=union(S1_5594,S2_5598,{v_5590}) & S2!=() & 
S3=S2_6088 & S3!=() & v_int_275_6075=v_6080 |-  union(S1,S2,S3,{0},{0})=union(S1_6084,S2_6088,{v_6080}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(568::,1 ); (568::,1 ); (562::,0 ); (562::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S1_5867=S2_5899 & S2_5870=S3_5900 & S_5676!=() & S_5676=union(S1_5867,
S2_5870,{v_5864}) & S_5676=S1_5594 & S=S2_5598 & S=S4 & 
S5_6147=union(S1_5898,S2_5899,S3_5900,S4,{0},{0},{0}) & v_int_275_6150=0 & 
S3=S2_6163 & S3!=() & S1_6159=S5_6147 & S1=S1_5898 & S2!=() & 
S2=union(S1_5594,S2_5598,{v_5590}) & v_int_275_6150=v_6155 |-  union(S1,S2,S3,{0},{0})=union(S1_6159,S2_6163,{v_6155}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]
Successful States:


Context of Verification Failure: File "rb_mhb.ss",Line:261,Col:9
Last Proving Location: File "rb_mhb.ss",Line:274,Col:23

ERROR: at rb_mhb.ss_261_9 
Message: Post condition cannot be derived by the system.
 
Procedure del_2_1$node~node~node FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure del_2_1$node~node~node

Checking procedure del_4r_1$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_4r_1$node~node~node SUCCESS

Checking procedure del_6r_1$node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_6r_1$node~node~node~int SUCCESS

Checking procedure del_5r_1$node~node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_5r_1$node~node~node~node~int SUCCESS

Checking procedure del_2r_1$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

assert/assume:rb_mhb.ss:295: 1:  : failed


assert/assume:rb_mhb.ss:296: 1:  : failed


assert:rb_mhb.ss:297: 1:  : ok


[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

( [(543::,0 ); (543::,0 ); (538::,0 ); (538::,0 )]) :rb_mhb.ss:281: 9: Postcondition cannot be derived from context


(Cause of PostCond Failure):rb_mhb.ss:281: 9:  List of Partial Context: [PC(3, 0)]
Failed States:
[
 Label: [(543::,0 ); (543::,0 ); (538::,0 ); (538::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  v_int_298_8491=0 & S2_7642=S_7720 & S2_7642=S2_7789 & S1_7638=S & 
S1_7638=S1_7788 & S4_8490=union(S1_7788,S2_7789,S3_7790,{0},{0}) & 
v_int_298_8491=v_8496 & S1=S1_8500 & S1!=() & S2_8504=S4_8490 & S3_7790=S3 & 
S2=union(S1_7638,S2_7642,{v_7634}) & S2!=() |-  union(S1,S2,S3,{0},{0})=union(S1_8500,S2_8504,{v_8496}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(543::,1 ); (543::,1 ); (538::,0 ); (538::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S1_7918=S2_7946 & S2_7921=S3_7947 & S_7720!=() & S_7720=union(S1_7918,
S2_7921,{v_7915}) & v_int_298_8566=0 & S_7720=S2_7642 & S=S1_7638 & 
S=S1_7945 & S5_8563=union(S1_7945,S2_7946,S3_7947,S4,{0},{0},{0}) & 
v_int_298_8566=v_8571 & S2_8579=S5_8563 & S3=S4 & S2=union(S1_7638,S2_7642,
{v_7634}) & S2!=() & S1=S1_8575 & S1!=() |-  union(S1,S2,S3,{0},{0})=union(S1_8575,S2_8579,{v_8571}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(538::,1 ); (538::,1 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  v_int_298_8641=0 & S1_8088=S1_7638 & S1_8088=S & S2_7642=S2_8089 & 
S1_7638!=() & S4_8638=union(S1_8088,S2_8089,S3_8090,{0},{0}) & 
v_int_298_8641=v_8646 & S1=S1_8650 & S1!=() & S2_8654=S4_8638 & S3=S3_8090 & 
S2=union(S1_7638,S2_7642,{v_7634}) & S2!=() |-  union(S1,S2,S3,{0},{0})=union(S1_8650,S2_8654,{v_8646}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]
Successful States:


Context of Verification Failure: File "rb_mhb.ss",Line:281,Col:9
Last Proving Location: File "rb_mhb.ss",Line:297,Col:1

ERROR: at rb_mhb.ss_281_9 
Message: Post condition cannot be derived by the system.
 
Procedure del_2r_1$node~node~node FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure del_2r_1$node~node~node

Checking procedure del_3_1$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_3_1$node~node~node SUCCESS

Checking procedure del_3r_1$node~node~node... 
Procedure del_3r_1$node~node~node SUCCESS

Checking procedure is_red_1$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  RED2(S2,S)
!!! POST:  S2=S
!!! PRE :  true
!!! REL :  RED1(S1,S)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RED1,RED2]
              EBase exists (Expl)(Impl)[cl; bh; 
                    S](ex)x::rb1<cl,bh,S>@M[Orig][LHSCase]@ rem br[{689,688,687}]&
                    (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::
                                
                                EXISTS(cl_324,bh_325,
                                S1: x::rb1<cl_324,bh_325,S1>@M[Orig][LHSCase]@ rem br[{688}]&
                                (
                                ([res][S1!=() & RED1(S1,S)][cl=cl_324 & cl=1]
                                 [bh=bh_325 & 1<=bh_325][null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl_326,bh_327,
                                   S2: x::rb1<cl_326,bh_327,S2>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                   (
                                   ([!(res)][RED2(S2,S)][cl=cl_326 & cl=0]
                                    [bh=bh_327 & 1<=bh_327]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl; bh; 
                  S](ex)x::rb1<cl,bh,S>@M[Orig][LHSCase]@ rem br[{689,688,687}]&
                  (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::
                              
                              EXISTS(cl_9262,bh_9263,
                              S1_9264: x::rb1<cl_9262,bh_9263,S1_9264>@M[Orig][LHSCase]@ rem br[{688}]&
                              (
                              ([S=S1_9264 & S1_9264!=()][null!=x]
                               [bh=bh_9263 & 1<=bh]
                               [1=cl & 1=cl_9262 & 0<=cl & cl<=1][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_9265,bh_9266,
                                 S2_9267: x::rb1<cl_9265,bh_9266,S2_9267>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                 (
                                 ([S=S2_9267][bh=bh_9266 & 1<=bh]
                                  [0=cl & 0=cl_9265 & 0<=cl & cl<=1][
                                  !(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S=S2) --> RED2(S2,S),
 (S=S2 & S2=) --> RED2(S2,S),
 (exists(S1_9149:exists(S2_9153:exists(v_9145:exists(S1_9080:exists(S2_9084:exists(v_9076:S1_9149=S1_9080 & 
  v_9076=v_9145 & S2_9084=S2_9153 & S2=union(S1_9149,S2_9153,{v_9145}) & 
  S!=() & S=union(S1_9080,S2_9084,{v_9076})))))))) --> RED2(S2,S),
 (exists(S1_9060:exists(S2_9063:exists(v_9057:exists(S1_9195:exists(S2_9198:exists(v_9192:S1_9195=S1_9060 & 
  v_9057=v_9192 & S2_9063=S2_9198 & S!=() & S=union(S1_9060,S2_9063,
  {v_9057}) & S1=union(S1_9195,S2_9198,{v_9192})))))))) --> RED1(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_red_1$node SUCCESS

Checking procedure remove_min_1$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure remove_min_1$node SUCCESS

Checking procedure del_1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_1$node~int SUCCESS

Checking procedure insert_1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure Call:rb_mhb.ss:521: 8: 
Verification Context:(Line:503,Col:9)
Proving precondition in method is_red_1$node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[cl; bh_14101; 
                  S_14102](ex)v_node_521_1014'::rb1<cl,bh_14101,S_14102>@M[Orig][LHSCase]@ rem br[{689,688,687}]&
                  (([1<=bh_14101][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::
                              
                              EXISTS(cl_9262,bh_9263,
                              S1_9264: v_node_521_1014'::rb1<cl_9262,bh_9263,S1_9264>@M[Orig][LHSCase]@ rem br[{688}]&
                              (
                              ([S1_9264=S_14102 & S1_9264!=()]
                               [null!=v_node_521_1014']
                               [bh_9263=bh_14101 & 1<=bh_14101]
                               [1=cl & 1=cl_9262 & 0<=cl & cl<=1][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_9265,bh_9266,
                                 S2_9267: v_node_521_1014'::rb1<cl_9265,bh_9266,S2_9267>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                 (
                                 ([S2_9267=S_14102]
                                  [bh_9266=bh_14101 & 1<=bh_14101]
                                  [0=cl & 0=cl_9265 & 0<=cl & cl<=1][
                                  !(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
Current States: [ r_13969::rb1<Anon_13970,bhr_13971,S2_13972>@M[Orig]@ rem br[{689,688,687}] * v_node_516_14080::rb1<Anon_14058,bh1_14059,S1_14060>@M[Orig][LHSCase]@ rem br[{688,687}] * x'::node<v_13964,color_516_14079,v_node_516_14080,r_13969>@M[Orig][]&(([
                                                                    tmp_107'=l_13965]
                                                                    [v_bool_513_1341']
                                                                    [Anon_18=0 & 
                                                                    0<=Anon_18 & 
                                                                    Anon_18<=1]
                                                                    [bh_14006=bhl_13967 & 
                                                                    bh_14006=bhr_13971 & 
                                                                    1<=bhl_13967 & 
                                                                    -1+
                                                                    bh=bhl_13967 & 
                                                                    bh1_14059<=bh_14006 & 
                                                                    bh_14006<=bh1_14059]
                                                                    [S_14007=S1_13968 & 
                                                                    v'=v & 
                                                                    S1_14060=union(S_14007,
                                                                    {v'}) & 
                                                                    S!=() & 
                                                                    v'<=v_13964 & 
                                                                    S=union(S1_13968,
                                                                    S2_13972,
                                                                    {v_13964})]
                                                                    [x'=x & 
                                                                    x'!=null]
                                                                    [Anon_13966<=1 & 
                                                                    0<=Anon_13966 & 
                                                                    Anon_14005=Anon_13966 & 
                                                                    Anon_14005<=1 & 
                                                                    0<=Anon_14005]
                                                                    [Anon_13970<=1 & 
                                                                    0<=Anon_13970]
                                                                    [null=tmp_108']
                                                                    [!(v_bool_508_1342')]
                                                                    [v_node_521_1014'=v_node_516_14080 & 
                                                                    null!=v_node_516_14080]
                                                                    [0=flted_13_13963 & 
                                                                    0=color_516_14079]
                                                                    [v_bool_519_1167']
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure Call:rb_mhb.ss:571: 8: 
Verification Context:(Line:503,Col:9)
Proving precondition in method is_red_1$node for spec:
 ((None,[]),EBase exists (Expl)(Impl)[cl; bh_14308; 
                  S_14309](ex)v_node_571_1187'::rb1<cl,bh_14308,S_14309>@M[Orig][LHSCase]@ rem br[{689,688,687}]&
                  (([1<=bh_14308][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::
                              
                              EXISTS(cl_9262,bh_9263,
                              S1_9264: v_node_571_1187'::rb1<cl_9262,bh_9263,S1_9264>@M[Orig][LHSCase]@ rem br[{688}]&
                              (
                              ([S1_9264=S_14309 & S1_9264!=()]
                               [null!=v_node_571_1187']
                               [bh_9263=bh_14308 & 1<=bh_14308]
                               [1=cl & 1=cl_9262 & 0<=cl & cl<=1][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_9265,bh_9266,
                                 S2_9267: v_node_571_1187'::rb1<cl_9265,bh_9266,S2_9267>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                 (
                                 ([S2_9267=S_14309]
                                  [bh_9266=bh_14308 & 1<=bh_14308]
                                  [0=cl & 0=cl_9265 & 0<=cl & cl<=1][
                                  !(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
Current States: [ l_13965::rb1<Anon_13966,bhl_13967,S1_13968>@M[Orig]@ rem br[{689,688,687}] * v_node_566_14274::rb1<Anon_14248,bh1_14249,S1_14250>@M[Orig][LHSCase]@ rem br[{688,687}] * x'::node<v_13964,color_566_14273,l_13965,v_node_566_14274>@M[Orig][]&(([
                                                                    tmp_107'=r_13969]
                                                                    [!(v_bool_513_1341')]
                                                                    [Anon_18=0 & 
                                                                    0<=Anon_18 & 
                                                                    Anon_18<=1]
                                                                    [bh_14184=bhr_13971 & 
                                                                    bh_14184=bhl_13967 & 
                                                                    1<=bhl_13967 & 
                                                                    -1+
                                                                    bh=bhl_13967 & 
                                                                    bh1_14249<=bh_14184 & 
                                                                    bh_14184<=bh1_14249]
                                                                    [S_14185=S2_13972 & 
                                                                    v'=v & 
                                                                    S1_14250=union(S_14185,
                                                                    {v'}) & 
                                                                    S!=() & 
                                                                    (1+
                                                                    v_13964)<=v' & 
                                                                    S=union(S1_13968,
                                                                    S2_13972,
                                                                    {v_13964})]
                                                                    [x'=x & 
                                                                    x'!=null]
                                                                    [Anon_13966<=1 & 
                                                                    0<=Anon_13966]
                                                                    [Anon_13970<=1 & 
                                                                    0<=Anon_13970 & 
                                                                    Anon_14183=Anon_13970 & 
                                                                    Anon_14183<=1 & 
                                                                    0<=Anon_14183]
                                                                    [null=tmp_108']
                                                                    [!(v_bool_508_1342')]
                                                                    [v_node_571_1187'=v_node_566_14274 & 
                                                                    null!=v_node_566_14274]
                                                                    [0=flted_13_13963 & 
                                                                    0=color_566_14273]
                                                                    [v_bool_569_1340']
                                                                    ))&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure insert_1$node~int result FAIL-1

Checking procedure rotate_case_3$node~node~node... 
!!! REL :  ROT3(S4,S1,S2,S3)
!!! POST:  S1!=() & S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT3]
              EBase exists (Expl)(Impl)[S1; S2; bha; S3](ex)EXISTS(bha_437,
                    bha_438,flted_20_434,flted_20_435,
                    flted_20_436: a::rb1<flted_20_436,bha,S1>@M[Orig][LHSCase]@ rem br[{688}] * 
                    b::rb1<flted_20_435,bha_437,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    c::rb1<flted_20_434,bha_438,S3>@M[Orig][LHSCase]@ rem br[{689,687}]&
                    (
                    ([flted_20_436=1][flted_20_435=0][flted_20_434=0]
                     [bha=bha_438 & bha=bha_437 & 1<=bha_438][null!=a]
                     [S1!=()]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(flted_21_432,flted_21_433,
                                S4: res::rb1<flted_21_433,flted_21_432,S4>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                (
                                ([flted_21_433=0][-1+flted_21_432=bha]
                                 [ROT3(S4,S1,S2,S3)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; bha; 
                  S3](ex)a::rb1<flted_20_436,bha,S1>@M[Orig][LHSCase]@ rem br[{688}] * 
                  b::rb1<flted_20_435,bha_437,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  c::rb1<flted_20_434,bha_438,S3>@M[Orig][LHSCase]@ rem br[{689,687}]&
                  (
                  ([S1!=()][bha=bha_438 & bha=bha_437 & 1<=bha][a!=null]
                   [1=flted_20_436][0=flted_20_435][0=flted_20_434]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(flted_21_14513,flted_21_14514,
                              S4_14515: res::rb1<flted_21_14514,flted_21_14513,S4_14515>@M[Orig][LHSCase]@ rem br[{689,687}]&
                              (
                              ([S1!=() & S4_14515=union(S1,S2,S3,{0},{0})]
                               [-1+flted_21_14513=bha & 1<=bha]
                               [0=flted_21_14514][1<=bha_438]
                               [0<=flted_20_434 & flted_20_434<=1]
                               [1<=bha_437]
                               [0<=flted_20_435 & flted_20_435<=1]
                               [0<=flted_20_436 & flted_20_436<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_14453:exists(S2_14459:exists(S1_14456:exists(S1_14431:exists(S2_14435:exists(v_14427:v_14453=0 & 
  S2_14435=union(S1_14456,S2_14459,{v_14453}) & v_14427=0 & S1_14431=S1 & 
  S3=S2_14459 & S2=S1_14456 & S1!=() & S4=union(S1_14431,S2_14435,
  {v_14427})))))))) --> ROT3(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  ROT3R(S4,S1,S2,S3)
!!! POST:  S3!=() & S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT3R]
              EBase exists (Expl)(Impl)[S1; S2; bha; S3](ex)EXISTS(bha_381,
                    bha_382,flted_62_378,flted_62_379,
                    flted_62_380: a::rb1<flted_62_380,bha,S1>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    b::rb1<flted_62_379,bha_381,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                    c::rb1<flted_62_378,bha_382,S3>@M[Orig][LHSCase]@ rem br[{688}]&
                    (
                    ([flted_62_380=0][flted_62_379=0][flted_62_378=1]
                     [bha=bha_382 & bha=bha_381 & 1<=bha_382][null!=c]
                     [S3!=()]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::
                                EXISTS(flted_63_376,flted_63_377,
                                S4: res::rb1<flted_63_377,flted_63_376,S4>@M[Orig][LHSCase]@ rem br[{689,687}]&
                                (
                                ([flted_63_377=0][-1+flted_63_376=bha]
                                 [ROT3R(S4,S1,S2,S3)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; bha; 
                  S3](ex)a::rb1<flted_62_380,bha,S1>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  b::rb1<flted_62_379,bha_381,S2>@M[Orig][LHSCase]@ rem br[{689,687}] * 
                  c::rb1<flted_62_378,bha_382,S3>@M[Orig][LHSCase]@ rem br[{688}]&
                  (
                  ([S3!=()][bha=bha_382 & bha=bha_381 & 1<=bha][c!=null]
                   [0=flted_62_380][0=flted_62_379][1=flted_62_378]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::
                              EXISTS(flted_63_14652,flted_63_14653,
                              S4_14654: res::rb1<flted_63_14653,flted_63_14652,S4_14654>@M[Orig][LHSCase]@ rem br[{689,687}]&
                              (
                              ([S3!=() & S4_14654=union(S1,S2,{0},S3,{0})]
                               [-1+flted_63_14652=bha & 1<=bha]
                               [0=flted_63_14653][1<=bha_382]
                               [0<=flted_62_378 & flted_62_378<=1]
                               [1<=bha_381]
                               [0<=flted_62_379 & flted_62_379<=1]
                               [0<=flted_62_380 & flted_62_380<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_14592:exists(S2_14598:exists(S1_14595:exists(S1_14570:exists(S2_14574:exists(v_14566:v_14592=0 & 
  S1_14570=union(S1_14595,S2_14598,{v_14592}) & v_14566=0 & S2_14574=S3 & 
  S2=S2_14598 & S1=S1_14595 & S3!=() & S4=union(S1_14570,S2_14574,
  {v_14566})))))))) --> ROT3R(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:


231 false contexts at: ( (607,4)  (561,4)  (468,4)  (490,12)  (490,57)  (490,42)  (490,28)  (490,20)  (490,8)  (487,13)  (487,83)  (487,68)  (487,48)  (487,29)  (487,21)  (487,9)  (484,14)  (484,44)  (484,30)  (484,22)  (484,10)  (482,14)  (482,44)  (482,30)  (482,22)  (482,10)  (481,24)  (481,13)  (481,13)  (481,9)  (479,23)  (479,12)  (479,8)  (478,22)  (478,11)  (478,7)  (474,12)  (474,42)  (474,28)  (474,20)  (474,8)  (473,11)  (473,11)  (473,7)  (471,19)  (471,10)  (471,6)  (470,20)  (470,9)  (470,5)  (468,8)  (468,24)  (468,21)  (439,4)  (459,12)  (459,57)  (459,48)  (459,34)  (459,21)  (459,8)  (457,13)  (457,83)  (457,74)  (457,54)  (457,35)  (457,22)  (457,9)  (455,14)  (455,50)  (455,36)  (455,23)  (455,10)  (453,14)  (453,50)  (453,36)  (453,23)  (453,10)  (452,24)  (452,13)  (452,13)  (452,9)  (451,23)  (451,12)  (451,8)  (450,22)  (450,11)  (450,7)  (445,12)  (445,48)  (445,34)  (445,21)  (445,8)  (444,11)  (444,11)  (444,7)  (442,19)  (442,10)  (442,6)  (441,20)  (441,9)  (441,5)  (439,8)  (439,25)  (439,22)  (405,4)  (425,12)  (425,57)  (425,48)  (425,34)  (425,21)  (425,8)  (423,13)  (423,83)  (423,74)  (423,54)  (423,35)  (423,22)  (423,9)  (421,14)  (421,50)  (421,36)  (421,23)  (421,10)  (419,14)  (419,50)  (419,36)  (419,23)  (419,10)  (418,24)  (418,13)  (418,13)  (418,9)  (417,23)  (417,12)  (417,8)  (416,22)  (416,11)  (416,7)  (412,12)  (412,48)  (412,34)  (412,21)  (412,8)  (411,11)  (411,11)  (411,7)  (409,19)  (409,10)  (409,6)  (407,20)  (407,9)  (407,5)  (405,8)  (405,25)  (405,22)  (377,3)  (377,10)  (374,4)  (374,11)  (368,6)  (368,13)  (367,10)  (367,55)  (367,40)  (367,26)  (367,18)  (367,6)  (367,6)  (362,7)  (362,14)  (361,11)  (361,81)  (361,66)  (361,46)  (361,27)  (361,19)  (361,7)  (361,7)  (357,8)  (357,15)  (356,12)  (356,42)  (356,28)  (356,20)  (356,8)  (356,8)  (352,8)  (352,15)  (351,12)  (351,42)  (351,28)  (351,20)  (351,8)  (351,8)  (349,22)  (349,11)  (349,11)  (349,7)  (348,21)  (348,10)  (348,6)  (346,20)  (346,9)  (346,5)  (342,6)  (342,13)  (339,48)  (339,55)  (338,10)  (338,40)  (338,26)  (338,18)  (338,6)  (338,6)  (336,9)  (336,9)  (336,5)  (334,17)  (334,8)  (334,4)  (332,18)  (332,7)  (332,3)  (330,6)  (330,22)  (330,19)  (274,23)  (274,51)  (274,42)  (274,34)  (274,17) )

Total verification time: 6.67 second(s)
	Time spent in main process: 3.45 second(s)
	Time spent in child processes: 3.22 second(s)
