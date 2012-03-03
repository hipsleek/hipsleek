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

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure case_2$node~node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  ROT2(S5,S1,S2,S3,S4)
!!! POST:  S5=union(S1,S2,{0},S3,S4,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT2]
              EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                    S4](ex)EXISTS(bha_491,bha_492,bha_493,flted_42_487,
                    flted_42_488,flted_42_489,
                    flted_42_490: a::rb1<flted_42_490,bha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_42_489,bha_491,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_42_488,bha_492,S3>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    d::rb1<flted_42_487,bha_493,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_42_490=0][flted_42_489=0][flted_42_488=0]
                     [flted_42_487=0]
                     [bha=bha_493 & bha=bha_492 & bha=bha_491 & 1<=bha_493]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 4::
                                EXISTS(flted_43_485,flted_43_486,
                                S5: res::rb1<flted_43_486,flted_43_485,S5>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_43_486=0][-1+flted_43_485=bha]
                                 [ROT2(S5,S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                  S4](ex)a::rb1<flted_42_490,bha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_42_489,bha_491,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_42_488,bha_492,S3>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  d::rb1<flted_42_487,bha_493,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([bha_492=bha & bha_492=bha_493 & bha_492=bha_491 & 
                     1<=bha_492]
                   [0=flted_42_490][0=flted_42_489][0=flted_42_488]
                   [0=flted_42_487]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 4::
                              EXISTS(flted_43_4169,flted_43_4170,
                              S5_4171: res::rb1<flted_43_4170,flted_43_4169,S5_4171>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S5_4171=union(S1,S2,{0},S3,S4,{0},{0})]
                               [-1+flted_43_4169=bha & 1<=bha]
                               [0=flted_43_4170][1<=bha_493]
                               [0<=flted_42_487 & flted_42_487<=1]
                               [1<=bha_492]
                               [0<=flted_42_488 & flted_42_488<=1]
                               [1<=bha_491]
                               [0<=flted_42_489 & flted_42_489<=1]
                               [0<=flted_42_490 & flted_42_490<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_4056:exists(v_4083:exists(S4_4158:exists(S3_4059:exists(S2_4057:exists(S2_4089:exists(S1_4086:v_4083=0 & 
  S4_4158=union(S1_4056,S2_4057,S3_4059,{0},{0}) & S1_4056=union(S1_4086,
  S2_4089,{v_4083}) & S4_4158=S5 & S4=S3_4059 & S3=S2_4057 & S2=S2_4089 & 
  S1=S1_4086)))))))) --> ROT2(S5,S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2$node~node~node~node SUCCESS

Checking procedure case_2r$node~node~node~node... 
!!! REL :  ROT2R(S5,S1,S2,S3,S4)
!!! POST:  S5=union(S1,S2,S3,S4,{0},{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT2R]
              EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                    S4](ex)EXISTS(bha_435,bha_436,bha_437,flted_82_431,
                    flted_82_432,flted_82_433,
                    flted_82_434: a::rb1<flted_82_434,bha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_82_433,bha_435,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_82_432,bha_436,S3>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    d::rb1<flted_82_431,bha_437,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_82_434=0][flted_82_433=0][flted_82_432=0]
                     [flted_82_431=0]
                     [bha=bha_437 & bha=bha_436 & bha=bha_435 & 1<=bha_437]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 10::
                                EXISTS(flted_83_429,flted_83_430,
                                S5: res::rb1<flted_83_430,flted_83_429,S5>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_83_430=0][-1+flted_83_429=bha]
                                 [ROT2R(S5,S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; S3; bha; 
                  S4](ex)a::rb1<flted_82_434,bha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_82_433,bha_435,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_82_432,bha_436,S3>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  d::rb1<flted_82_431,bha_437,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([bha_436=bha & bha_436=bha_437 & bha_436=bha_435 & 
                     1<=bha_436]
                   [0=flted_82_434][0=flted_82_433][0=flted_82_432]
                   [0=flted_82_431]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 10::
                              EXISTS(flted_83_4294,flted_83_4295,
                              S5_4296: res::rb1<flted_83_4295,flted_83_4294,S5_4296>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S5_4296=union(S1,S2,S3,S4,{0},{0},{0})]
                               [-1+flted_83_4294=bha & 1<=bha]
                               [0=flted_83_4295][1<=bha_437]
                               [0<=flted_82_431 & flted_82_431<=1]
                               [1<=bha_436]
                               [0<=flted_82_432 & flted_82_432<=1]
                               [1<=bha_435]
                               [0<=flted_82_433 & flted_82_433<=1]
                               [0<=flted_82_434 & flted_82_434<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S3_4195:exists(v_4222:exists(S4_4283:exists(S1_4192:exists(S2_4193:exists(S2_4228:exists(S1_4225:v_4222=0 & 
  S4_4283=union(S1_4192,S2_4193,S3_4195,{0},{0}) & S3_4195=union(S1_4225,
  S2_4228,{v_4222}) & S4_4283=S5 & S1=S1_4192 & S2_4193=S2 & S4=S2_4228 & 
  S3=S1_4225)))))))) --> ROT2R(S5,S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure case_2r$node~node~node~node SUCCESS

Checking procedure del_5_1$node~node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure del_5_1$node~node~node~node~int SUCCESS

Checking procedure del_2_1$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

( [(575::,0 ); (575::,0 ); (569::,0 ); (569::,0 )]) :rb_mhb.ss:307: 9: Postcondition cannot be derived from context


(Cause of PostCond Failure):rb_mhb.ss:307: 9:  List of Partial Context: [PC(2, 0)]
Failed States:
[
 Label: [(575::,0 ); (575::,0 ); (569::,0 ); (569::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S2_4799=S & S2_4799=S3_4947 & S1_4795=S_4877 & S1_4795=S2_4946 & 
S4_5275=union(S1_4945,S2_4946,S3_4947,{0},{0}) & v_int_321_5276=0 & 
S1_5285=S4_5275 & S1_4945=S1 & S2=union(S1_4795,S2_4799,{v_4791}) & S2!=() & 
S3=S2_5289 & S3!=() & v_int_321_5276=v_5281 |-  union(S1,S2,S3,{0},{0})=union(S1_5285,S2_5289,{v_5281}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(575::,1 ); (575::,1 ); (569::,0 ); (569::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S1_5068=S2_5100 & S2_5071=S3_5101 & S_4877!=() & S_4877=union(S1_5068,
S2_5071,{v_5065}) & S_4877=S1_4795 & S=S2_4799 & S=S4 & 
S5_5348=union(S1_5099,S2_5100,S3_5101,S4,{0},{0},{0}) & v_int_321_5351=0 & 
S3=S2_5364 & S3!=() & S1_5360=S5_5348 & S1=S1_5099 & S2!=() & 
S2=union(S1_4795,S2_4799,{v_4791}) & v_int_321_5351=v_5356 |-  union(S1,S2,S3,{0},{0})=union(S1_5360,S2_5364,{v_5356}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]
Successful States:


Context of Verification Failure: File "rb_mhb.ss",Line:307,Col:9
Last Proving Location: File "rb_mhb.ss",Line:320,Col:23

ERROR: at rb_mhb.ss_307_9 
Message: Post condition cannot be derived by the system.
 
Procedure del_2_1$node~node~node FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure del_2_1$node~node~node

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

assert/assume:rb_mhb.ss:341: 1:  : failed


[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

assert/assume:rb_mhb.ss:342: 1:  : failed


assert:rb_mhb.ss:343: 1:  : ok


[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

( [(550::,0 ); (550::,0 ); (545::,0 ); (545::,0 )]) :rb_mhb.ss:327: 9: Postcondition cannot be derived from context


(Cause of PostCond Failure):rb_mhb.ss:327: 9:  List of Partial Context: [PC(3, 0)]
Failed States:
[
 Label: [(550::,0 ); (550::,0 ); (545::,0 ); (545::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  v_int_344_7551=0 & S2_6702=S_6780 & S2_6702=S2_6849 & S1_6698=S & 
S1_6698=S1_6848 & S4_7550=union(S1_6848,S2_6849,S3_6850,{0},{0}) & 
v_int_344_7551=v_7556 & S1=S1_7560 & S1!=() & S2_7564=S4_7550 & S3_6850=S3 & 
S2=union(S1_6698,S2_6702,{v_6694}) & S2!=() |-  union(S1,S2,S3,{0},{0})=union(S1_7560,S2_7564,{v_7556}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(550::,1 ); (550::,1 ); (545::,0 ); (545::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S1_6978=S2_7006 & S2_6981=S3_7007 & S_6780!=() & S_6780=union(S1_6978,
S2_6981,{v_6975}) & v_int_344_7626=0 & S_6780=S2_6702 & S=S1_6698 & 
S=S1_7005 & S5_7623=union(S1_7005,S2_7006,S3_7007,S4,{0},{0},{0}) & 
v_int_344_7626=v_7631 & S2_7639=S5_7623 & S3=S4 & S2=union(S1_6698,S2_6702,
{v_6694}) & S2!=() & S1=S1_7635 & S1!=() |-  union(S1,S2,S3,{0},{0})=union(S1_7635,S2_7639,{v_7631}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(545::,1 ); (545::,1 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  v_int_344_7701=0 & S1_7148=S1_6698 & S1_7148=S & S2_6702=S2_7149 & 
S1_6698!=() & S4_7698=union(S1_7148,S2_7149,S3_7150,{0},{0}) & 
v_int_344_7701=v_7706 & S1=S1_7710 & S1!=() & S2_7714=S4_7698 & S3=S3_7150 & 
S2=union(S1_6698,S2_6702,{v_6694}) & S2!=() |-  union(S1,S2,S3,{0},{0})=union(S1_7710,S2_7714,{v_7706}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]
Successful States:


Context of Verification Failure: File "rb_mhb.ss",Line:327,Col:9
Last Proving Location: File "rb_mhb.ss",Line:343,Col:1

ERROR: at rb_mhb.ss_327_9 
Message: Post condition cannot be derived by the system.
 
Procedure del_2r_1$node~node~node FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure del_2r_1$node~node~node

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

Checking procedure del_3$node~node~node... 
!!! REL :  DEL3(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL3]
              EBase exists (Expl)(Impl)[S1; S2; ha; S3](ex)EXISTS(ha_211,
                    ha_212,flted_270_208,flted_270_209,
                    flted_270_210: a::rb1<flted_270_210,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_270_209,ha_211,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_270_208,ha_212,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_270_210=0][flted_270_209=0][flted_270_208=0]
                     [ha=ha_212 & ha=ha_211 & 1<=ha_212]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_271_206,flted_271_207,
                                S4: res::rb1<flted_271_207,flted_271_206,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_271_207=0][-1+flted_271_206=ha]
                                 [DEL3(S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; ha; 
                  S3](ex)a::rb1<flted_270_210,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_270_209,ha_211,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_270_208,ha_212,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([ha_211=ha & ha_211=ha_212 & 1<=ha_211][0=flted_270_210]
                   [0=flted_270_209][0=flted_270_208]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_271_12511,flted_271_12512,
                              S4_12513: res::rb1<flted_271_12512,flted_271_12511,S4_12513>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12513=union(S1,S2,S3,{0},{0})]
                               [-1+flted_271_12511=ha & 1<=ha]
                               [0=flted_271_12512][1<=ha_212]
                               [0<=flted_270_208 & flted_270_208<=1]
                               [1<=ha_211]
                               [0<=flted_270_209 & flted_270_209<=1]
                               [0<=flted_270_210 & flted_270_210<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12451:exists(S2_12457:exists(S1_12454:exists(S1_12429:exists(S2_12433:exists(v_12425:v_12451=0 & 
  S2_12433=union(S1_12454,S2_12457,{v_12451}) & v_12425=0 & S1_12429=S1 & 
  S3=S2_12457 & S2=S1_12454 & S4=union(S1_12429,S2_12433,
  {v_12425})))))))) --> DEL3(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3$node~node~node SUCCESS

Checking procedure del_3r$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL3R(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL3R]
              EBase exists (Expl)(Impl)[S1; S2; ha; S3](ex)EXISTS(ha_186,
                    ha_187,flted_288_183,flted_288_184,
                    flted_288_185: a::rb1<flted_288_185,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_288_184,ha_186,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_288_183,ha_187,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_288_185=0][flted_288_184=0][flted_288_183=0]
                     [ha=ha_187 & ha=ha_186 & 1<=ha_187]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                EXISTS(flted_289_181,flted_289_182,
                                S4: res::rb1<flted_289_182,flted_289_181,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_289_182=0][-1+flted_289_181=ha]
                                 [DEL3R(S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; ha; 
                  S3](ex)a::rb1<flted_288_185,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_288_184,ha_186,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_288_183,ha_187,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([ha_186=ha & ha_186=ha_187 & 1<=ha_186][0=flted_288_185]
                   [0=flted_288_184][0=flted_288_183]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              EXISTS(flted_289_12650,flted_289_12651,
                              S4_12652: res::rb1<flted_289_12651,flted_289_12650,S4_12652>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12652=union(S1,S2,{0},S3,{0})]
                               [-1+flted_289_12650=ha & 1<=ha]
                               [0=flted_289_12651][1<=ha_187]
                               [0<=flted_288_183 & flted_288_183<=1]
                               [1<=ha_186]
                               [0<=flted_288_184 & flted_288_184<=1]
                               [0<=flted_288_185 & flted_288_185<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12590:exists(S2_12596:exists(S1_12593:exists(S1_12568:exists(S2_12572:exists(v_12564:v_12590=0 & 
  S1_12568=union(S1_12593,S2_12596,{v_12590}) & v_12564=0 & S3=S2_12572 & 
  S2=S2_12596 & S1=S1_12593 & S4=union(S1_12568,S2_12572,
  {v_12564})))))))) --> DEL3R(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_3r$node~node~node SUCCESS

Checking procedure del_4$node~node~node... 
!!! REL :  DEL4(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL4]
              EBase exists (Expl)(Impl)[S1; S2; ha; S3](ex)EXISTS(ha_261,
                    ha_262,flted_230_258,flted_230_259,
                    flted_230_260: a::rb1<flted_230_260,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_230_259,ha_261,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_230_258,ha_262,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_230_260=0][flted_230_259=0][flted_230_258=0]
                     [ha=ha_262 & ha=ha_261 & 1<=ha_262]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 32::
                                EXISTS(flted_231_256,flted_231_257,
                                S4: res::rb1<flted_231_257,flted_231_256,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_231_257=0][-1+flted_231_256=ha]
                                 [DEL4(S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; ha; 
                  S3](ex)a::rb1<flted_230_260,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_230_259,ha_261,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_230_258,ha_262,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([ha_261=ha & ha_261=ha_262 & 1<=ha_261][0=flted_230_260]
                   [0=flted_230_259][0=flted_230_258]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 32::
                              EXISTS(flted_231_12789,flted_231_12790,
                              S4_12791: res::rb1<flted_231_12790,flted_231_12789,S4_12791>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12791=union(S1,S2,S3,{0},{0})]
                               [-1+flted_231_12789=ha & 1<=ha]
                               [0=flted_231_12790][1<=ha_262]
                               [0<=flted_230_258 & flted_230_258<=1]
                               [1<=ha_261]
                               [0<=flted_230_259 & flted_230_259<=1]
                               [0<=flted_230_260 & flted_230_260<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12729:exists(S2_12735:exists(S1_12732:exists(S1_12707:exists(S2_12711:exists(v_12703:v_12729=0 & 
  S2_12711=union(S1_12732,S2_12735,{v_12729}) & v_12703=0 & S1_12707=S1 & 
  S3=S2_12735 & S2=S1_12732 & S4=union(S1_12707,S2_12711,
  {v_12703})))))))) --> DEL4(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4$node~node~node SUCCESS

Checking procedure del_4r$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL4R(S1,S2,S3,S4)
!!! POST:  S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL4R]
              EBase exists (Expl)(Impl)[S1; S2; ha; S3](ex)EXISTS(ha_236,
                    ha_237,flted_248_233,flted_248_234,
                    flted_248_235: a::rb1<flted_248_235,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_248_234,ha_236,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_248_233,ha_237,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_248_235=0][flted_248_234=0][flted_248_233=0]
                     [ha=ha_237 & ha=ha_236 & 1<=ha_237]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_249_231,flted_249_232,
                                S4: res::rb1<flted_249_232,flted_249_231,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_249_232=0][-1+flted_249_231=ha]
                                 [DEL4R(S1,S2,S3,S4)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; ha; 
                  S3](ex)a::rb1<flted_248_235,ha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_248_234,ha_236,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_248_233,ha_237,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([ha_236=ha & ha_236=ha_237 & 1<=ha_236][0=flted_248_235]
                   [0=flted_248_234][0=flted_248_233]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(flted_249_12928,flted_249_12929,
                              S4_12930: res::rb1<flted_249_12929,flted_249_12928,S4_12930>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12930=union(S1,S2,{0},S3,{0})]
                               [-1+flted_249_12928=ha & 1<=ha]
                               [0=flted_249_12929][1<=ha_237]
                               [0<=flted_248_233 & flted_248_233<=1]
                               [1<=ha_236]
                               [0<=flted_248_234 & flted_248_234<=1]
                               [0<=flted_248_235 & flted_248_235<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12868:exists(S2_12874:exists(S1_12871:exists(S1_12846:exists(S2_12850:exists(v_12842:v_12868=0 & 
  S1_12846=union(S1_12871,S2_12874,{v_12868}) & v_12842=0 & S3=S2_12850 & 
  S2=S2_12874 & S1=S1_12871 & S4=union(S1_12846,S2_12850,
  {v_12842})))))))) --> DEL4R(S1,S2,S3,S4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_4r$node~node~node SUCCESS

Checking procedure del_6$node~node~node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  DEL61(S1,S2,S3,S4)
!!! POST:  S3!=()
!!! PRE :  true
!!! REL :  DEL62(S1,S2,S3,S5)
!!! POST:  S3!=()
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL61,DEL62]
              EBase exists (Expl)(Impl)[Anon_13; S1; Anon_14; S2; h; 
                    S3](ex)
                           EXISTS(h_383,h_384,flted_158_379,
                           flted_158_380: a::rb1<flted_158_380,h,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                           b::rb1<Anon_13,h_383,S2>@M[Orig][LHSCase]@ rem br[{696,695,694}] * 
                           c::rb1<flted_158_379,h_384,S3>@M[Orig][LHSCase]@ rem br[{695}]&
                           (
                           ([flted_158_380=0][flted_158_379=1][0=color]
                            [h=h_384 & h=h_383 & 1<=h_384]
                            [Anon_13<=1 & 0<=Anon_13][null!=c][S3!=()]))&
                           {FLOW,(20,21)=__norm})
                           or EXISTS(h_385,h_386,flted_159_381,
                              flted_159_382: a::rb1<flted_159_382,h,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                              b::rb1<Anon_14,h_385,S2>@M[Orig][LHSCase]@ rem br[{696,695,694}] * 
                              c::rb1<flted_159_381,h_386,S3>@M[Orig][LHSCase]@ rem br[{695}]&
                              (
                              ([flted_159_382=0][flted_159_381=1][1=color]
                               [h=h_386 & h=h_385 & 1<=h_386]
                               [Anon_14<=1 & 0<=Anon_14][null!=c][S3!=()]))&
                              {FLOW,(20,21)=__norm})
                           
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 21::
                                
                                EXISTS(flted_160_375,flted_160_376,
                                S4: res::rb1<flted_160_376,flted_160_375,S4>@M[Orig][LHSCase]@ rem br[{694}]&
                                (
                                ([flted_160_376=0][-2+flted_160_375=h]
                                 [S4!=() & DEL61(S1,S2,S3,S4)][0=color]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(flted_161_377,flted_161_378,
                                   S5: res::rb1<flted_161_378,flted_161_377,S5>@M[Orig][LHSCase]@ rem br[{695}]&
                                   (
                                   ([flted_161_378=1][-1+flted_161_377=h]
                                    [S5!=() & DEL62(S1,S2,S3,S5)][1=color]
                                    [null!=res]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_13; S1; Anon_14; S2; h; 
                  S3](ex)
                         a::rb1<flted_158_380,h,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                         b::rb1<Anon_13,h_383,S2>@M[Orig][LHSCase]@ rem br[{696,695,694}] * 
                         c::rb1<flted_158_379,h_384,S3>@M[Orig][LHSCase]@ rem br[{695}]&
                         (
                         ([S3!=()][h=h_384 & h=h_383 & 1<=h][c!=null]
                          [0=flted_158_380][1=flted_158_379][0=color]
                          [Anon_13<=1 & 0<=Anon_13]))&
                         {FLOW,(20,21)=__norm}
                         or a::rb1<flted_159_382,h,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                            b::rb1<Anon_14,h_385,S2>@M[Orig][LHSCase]@ rem br[{696,695,694}] * 
                            c::rb1<flted_159_381,h_386,S3>@M[Orig][LHSCase]@ rem br[{695}]&
                            (
                            ([S3!=()][h=h_386 & h=h_385 & 1<=h][c!=null]
                             [0=flted_159_382][1=flted_159_381][1=color]
                             [Anon_14<=1 & 0<=Anon_14]))&
                            {FLOW,(20,21)=__norm}
                         
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 21::
                              
                              EXISTS(flted_160_13674,flted_160_13675,
                              S4_13676: res::rb1<flted_160_13675,flted_160_13674,S4_13676>@M[Orig][LHSCase]@ rem br[{694}]&
                              (
                              ([S3!=()][null!=res][color=0][S4_13676!=()]
                               [(0<=flted_158_380 & flted_158_380<=1 & 
                                 1<=h & 0<=Anon_13 & Anon_13<=1 & 1<=h_383 & 
                                 0<=flted_158_379 & flted_158_379<=1 & 
                                 1<=h_384 | 0<=flted_159_382 & 
                                 flted_159_382<=1 & 1<=h & 0<=Anon_14 & 
                                 Anon_14<=1 & 1<=h_385 & 0<=flted_159_381 & 
                                 flted_159_381<=1 & 1<=h_386) & -2+
                                 flted_160_13674=h]
                               [0=flted_160_13675]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_161_13677,flted_161_13678,
                                 S5_13679: res::rb1<flted_161_13678,flted_161_13677,S5_13679>@M[Orig][LHSCase]@ rem br[{695}]&
                                 (
                                 ([S3!=()][null!=res][color=1][S5_13679!=()]
                                  [(0<=flted_158_380 & flted_158_380<=1 & 
                                    1<=h & 0<=Anon_13 & Anon_13<=1 & 
                                    1<=h_383 & 0<=flted_158_379 & 
                                    flted_158_379<=1 & 1<=h_384 | 
                                    0<=flted_159_382 & flted_159_382<=1 & 
                                    1<=h & 0<=Anon_14 & Anon_14<=1 & 
                                    1<=h_385 & 0<=flted_159_381 & 
                                    flted_159_381<=1 & 1<=h_386) & -1+
                                    flted_161_13677=h]
                                  [1=flted_161_13678]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(v_13125:exists(S2_13184:exists(v_13176:exists(S1_13180:exists(S2_13133:exists(S1_13129:exists(S1_13113:exists(S2_13117:exists(v_13109:exists(S1_13033:exists(S2_13036:exists(v_13030:v_13125=0 & 
  S2_13117=union(S1_13180,S2_13184,{v_13176}) & S1_13113=union(S1_13129,
  S2_13133,{v_13125}) & S2_13184=S2_13036 & v_13176=v_13030 & 
  S1_13033=S1_13180 & v_13109=0 & S2=S2_13133 & S1=S1_13129 & 
  S4=union(S1_13113,S2_13117,{v_13109}) & S3!=() & S3=union(S1_13033,
  S2_13036,{v_13030})))))))))))))) --> DEL61(S1,S2,S3,S4),
 (exists(v_13590:exists(S2_13625:exists(v_13617:exists(S1_13621:exists(S2_13598:exists(S1_13594:exists(S1_13575:exists(S2_13578:exists(v_13572:exists(S1_13057:exists(S2_13060:exists(v_13054:v_13590=0 & 
  S2_13578=union(S1_13621,S2_13625,{v_13617}) & S1_13575=union(S1_13594,
  S2_13598,{v_13590}) & S2_13625=S2_13060 & v_13617=v_13054 & 
  S1_13057=S1_13621 & v_13572=0 & S2=S2_13598 & S1=S1_13594 & 
  S5=union(S1_13575,S2_13578,{v_13572}) & S3!=() & S3=union(S1_13057,
  S2_13060,{v_13054})))))))))))))) --> DEL62(S1,S2,S3,S5)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure del_6$node~node~node~int SUCCESS

Checking procedure insert_1$node~int... 
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

!!! REL :  INS(S1,S,v)
!!! POST:  S= & S1={v} & forall(_x:_x <notin> S1  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[Anon_20; bh; 
                    S](ex)x::rb1<Anon_20,bh,S>@M[Orig][LHSCase]@ rem br[{696,695,694}]&
                    (([1<=bh][Anon_20<=1 & 0<=Anon_20]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 104::
                                EXISTS(Anon_21,bh1,
                                S1: res::rb1<Anon_21,bh1,S1>@M[Orig][LHSCase]@ rem br[{695,694}]&
                                (
                                ([null!=res][bh1<=bh & bh<=bh1]
                                 [S1!=() & INS(S1,S,v)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_20; bh; 
                  S](ex)x::rb1<Anon_20,bh,S>@M[Orig][LHSCase]@ rem br[{696,695,694}]&
                  (([1<=bh][Anon_20<=1 & 0<=Anon_20]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 104::
                              EXISTS(Anon_14675,bh1_14676,
                              S1_14677: res::rb1<Anon_14675,bh1_14676,S1_14677>@M[Orig][LHSCase]@ rem br[{695,694}]&
                              (
                              ([forall(_x:_x <notin> S1_14677  | _x=v) & 
                                 S1_14677!=() & S1_14677={v}]
                               [S=][bh1_14676<=bh & 1<=bh & bh<=bh1_14676]
                               [null!=res][Anon_20<=1 & 0<=Anon_20]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_14636:exists(S2_14639:exists(v_14633:S1_14636= & S2_14639= & 
  v_14633=v & S= & S1=union(S1_14636,S2_14639,{v_14633}))))) --> INS(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert_1$node~int SUCCESS

Checking procedure is_black$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  BLACK2(S2,S)
!!! POST:  S2=S
!!! PRE :  true
!!! REL :  BLACK1(S1,S)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [BLACK1,BLACK2]
              EBase exists (Expl)(Impl)[cl; bh; 
                    S](ex)x::rb1<cl,bh,S>@M[Orig][LHSCase]@ rem br[{696,695,694}]&
                    (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 17::
                                
                                EXISTS(cl_394,bh_395,
                                S1: x::rb1<cl_394,bh_395,S1>@M[Orig][LHSCase]@ rem br[{695}]&
                                (
                                ([!(res)][S1!=() & BLACK1(S1,S)]
                                 [cl=cl_394 & cl=1][bh=bh_395 & 1<=bh_395]
                                 [null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl_396,bh_397,
                                   S2: x::rb1<cl_396,bh_397,S2>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                   (
                                   ([res][BLACK2(S2,S)][cl=cl_396 & cl=0]
                                    [bh=bh_397 & 1<=bh_397]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl; bh; 
                  S](ex)x::rb1<cl,bh,S>@M[Orig][LHSCase]@ rem br[{696,695,694}]&
                  (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 17::
                              
                              EXISTS(cl_14950,bh_14951,
                              S1_14952: x::rb1<cl_14950,bh_14951,S1_14952>@M[Orig][LHSCase]@ rem br[{695}]&
                              (
                              ([S=S1_14952 & S1_14952!=()][null!=x]
                               [bh=bh_14951 & 1<=bh]
                               [1=cl & 1=cl_14950 & 0<=cl & cl<=1][!(res)]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_14953,bh_14954,
                                 S2_14955: x::rb1<cl_14953,bh_14954,S2_14955>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                 (
                                 ([S=S2_14955][bh=bh_14954 & 1<=bh]
                                  [0=cl & 0=cl_14953 & 0<=cl & cl<=1][
                                  res]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S=S2) --> BLACK2(S2,S),
 (S=S2 & S2=) --> BLACK2(S2,S),
 (exists(S1_14837:exists(S2_14841:exists(v_14833:exists(S1_14768:exists(S2_14772:exists(v_14764:S1_14837=S1_14768 & 
  v_14764=v_14833 & S2_14772=S2_14841 & S2=union(S1_14837,S2_14841,
  {v_14833}) & S!=() & S=union(S1_14768,S2_14772,
  {v_14764})))))))) --> BLACK2(S2,S),
 (exists(S1_14748:exists(S2_14751:exists(v_14745:exists(S1_14883:exists(S2_14886:exists(v_14880:S1_14883=S1_14748 & 
  v_14745=v_14880 & S2_14751=S2_14886 & S!=() & S=union(S1_14748,S2_14751,
  {v_14745}) & S1=union(S1_14883,S2_14886,{v_14880})))))))) --> BLACK1(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_black$node SUCCESS

Checking procedure is_red$node... 
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
                    S](ex)x::rb1<cl,bh,S>@M[Orig][LHSCase]@ rem br[{696,695,694}]&
                    (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::
                                
                                EXISTS(cl_404,bh_405,
                                S1: x::rb1<cl_404,bh_405,S1>@M[Orig][LHSCase]@ rem br[{695}]&
                                (
                                ([res][S1!=() & RED1(S1,S)][cl=cl_404 & cl=1]
                                 [bh=bh_405 & 1<=bh_405][null!=x]))&
                                {FLOW,(20,21)=__norm})
                                or EXISTS(cl_406,bh_407,
                                   S2: x::rb1<cl_406,bh_407,S2>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                   (
                                   ([!(res)][RED2(S2,S)][cl=cl_406 & cl=0]
                                    [bh=bh_407 & 1<=bh_407]))&
                                   {FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[cl; bh; 
                  S](ex)x::rb1<cl,bh,S>@M[Orig][LHSCase]@ rem br[{696,695,694}]&
                  (([1<=bh][cl<=1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 13::
                              
                              EXISTS(cl_15228,bh_15229,
                              S1_15230: x::rb1<cl_15228,bh_15229,S1_15230>@M[Orig][LHSCase]@ rem br[{695}]&
                              (
                              ([S=S1_15230 & S1_15230!=()][null!=x]
                               [bh=bh_15229 & 1<=bh]
                               [1=cl & 1=cl_15228 & 0<=cl & cl<=1][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_15231,bh_15232,
                                 S2_15233: x::rb1<cl_15231,bh_15232,S2_15233>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                 (
                                 ([S=S2_15233][bh=bh_15232 & 1<=bh]
                                  [0=cl & 0=cl_15231 & 0<=cl & cl<=1][
                                  !(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S=S2) --> RED2(S2,S),
 (S=S2 & S2=) --> RED2(S2,S),
 (exists(S1_15115:exists(S2_15119:exists(v_15111:exists(S1_15046:exists(S2_15050:exists(v_15042:S1_15115=S1_15046 & 
  v_15042=v_15111 & S2_15050=S2_15119 & S2=union(S1_15115,S2_15119,
  {v_15111}) & S!=() & S=union(S1_15046,S2_15050,
  {v_15042})))))))) --> RED2(S2,S),
 (exists(S1_15026:exists(S2_15029:exists(v_15023:exists(S1_15161:exists(S2_15164:exists(v_15158:S1_15161=S1_15026 & 
  v_15023=v_15158 & S2_15029=S2_15164 & S!=() & S=union(S1_15026,S2_15029,
  {v_15023}) & S1=union(S1_15161,S2_15164,{v_15158})))))))) --> RED1(S1,S)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure is_red$node SUCCESS

Checking procedure rotate_case_3$node~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  ROT3(S4,S1,S2,S3)
!!! POST:  S1!=() & S4=union(S1,S2,S3,{0},{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT3]
              EBase exists (Expl)(Impl)[S1; S2; bha; S3](ex)EXISTS(bha_517,
                    bha_518,flted_20_514,flted_20_515,
                    flted_20_516: a::rb1<flted_20_516,bha,S1>@M[Orig][LHSCase]@ rem br[{695}] * 
                    b::rb1<flted_20_515,bha_517,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_20_514,bha_518,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                    (
                    ([flted_20_516=1][flted_20_515=0][flted_20_514=0]
                     [bha=bha_518 & bha=bha_517 & 1<=bha_518][null!=a]
                     [S1!=()]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(flted_21_512,flted_21_513,
                                S4: res::rb1<flted_21_513,flted_21_512,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_21_513=0][-1+flted_21_512=bha]
                                 [ROT3(S4,S1,S2,S3)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; bha; 
                  S3](ex)a::rb1<flted_20_516,bha,S1>@M[Orig][LHSCase]@ rem br[{695}] * 
                  b::rb1<flted_20_515,bha_517,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_20_514,bha_518,S3>@M[Orig][LHSCase]@ rem br[{696,694}]&
                  (
                  ([S1!=()][bha=bha_518 & bha=bha_517 & 1<=bha][a!=null]
                   [1=flted_20_516][0=flted_20_515][0=flted_20_514]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(flted_21_15370,flted_21_15371,
                              S4_15372: res::rb1<flted_21_15371,flted_21_15370,S4_15372>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S1!=() & S4_15372=union(S1,S2,S3,{0},{0})]
                               [-1+flted_21_15370=bha & 1<=bha]
                               [0=flted_21_15371][1<=bha_518]
                               [0<=flted_20_514 & flted_20_514<=1]
                               [1<=bha_517]
                               [0<=flted_20_515 & flted_20_515<=1]
                               [0<=flted_20_516 & flted_20_516<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_15310:exists(S2_15316:exists(S1_15313:exists(S1_15288:exists(S2_15292:exists(v_15284:v_15310=0 & 
  S2_15292=union(S1_15313,S2_15316,{v_15310}) & v_15284=0 & S1_15288=S1 & 
  S3=S2_15316 & S2=S1_15313 & S1!=() & S4=union(S1_15288,S2_15292,
  {v_15284})))))))) --> ROT3(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3$node~node~node SUCCESS

Checking procedure rotate_case_3r$node~node~node... 
!!! REL :  ROT3R(S4,S1,S2,S3)
!!! POST:  S3!=() & S4=union(S1,S2,{0},S3,{0})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [ROT3R]
              EBase exists (Expl)(Impl)[S1; S2; bha; S3](ex)EXISTS(bha_461,
                    bha_462,flted_62_458,flted_62_459,
                    flted_62_460: a::rb1<flted_62_460,bha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    b::rb1<flted_62_459,bha_461,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                    c::rb1<flted_62_458,bha_462,S3>@M[Orig][LHSCase]@ rem br[{695}]&
                    (
                    ([flted_62_460=0][flted_62_459=0][flted_62_458=1]
                     [bha=bha_462 & bha=bha_461 & 1<=bha_462][null!=c]
                     [S3!=()]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 7::
                                EXISTS(flted_63_456,flted_63_457,
                                S4: res::rb1<flted_63_457,flted_63_456,S4>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                (
                                ([flted_63_457=0][-1+flted_63_456=bha]
                                 [ROT3R(S4,S1,S2,S3)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[S1; S2; bha; 
                  S3](ex)a::rb1<flted_62_460,bha,S1>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  b::rb1<flted_62_459,bha_461,S2>@M[Orig][LHSCase]@ rem br[{696,694}] * 
                  c::rb1<flted_62_458,bha_462,S3>@M[Orig][LHSCase]@ rem br[{695}]&
                  (
                  ([S3!=()][bha=bha_462 & bha=bha_461 & 1<=bha][c!=null]
                   [0=flted_62_460][0=flted_62_459][1=flted_62_458]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 7::
                              EXISTS(flted_63_15509,flted_63_15510,
                              S4_15511: res::rb1<flted_63_15510,flted_63_15509,S4_15511>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S3!=() & S4_15511=union(S1,S2,{0},S3,{0})]
                               [-1+flted_63_15509=bha & 1<=bha]
                               [0=flted_63_15510][1<=bha_462]
                               [0<=flted_62_458 & flted_62_458<=1]
                               [1<=bha_461]
                               [0<=flted_62_459 & flted_62_459<=1]
                               [0<=flted_62_460 & flted_62_460<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_15449:exists(S2_15455:exists(S1_15452:exists(S1_15427:exists(S2_15431:exists(v_15423:v_15449=0 & 
  S1_15427=union(S1_15452,S2_15455,{v_15449}) & v_15423=0 & S2_15431=S3 & 
  S2=S2_15455 & S1=S1_15452 & S3!=() & S4=union(S1_15427,S2_15431,
  {v_15423})))))))) --> ROT3R(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:


309 false contexts at: ( (655,4)  (652,5)  (648,7)  (645,8)  (645,15)  (644,12)  (644,51)  (644,37)  (644,29)  (644,8)  (644,8)  (640,8)  (640,15)  (639,24)  (639,8)  (638,23)  (638,8)  (638,8)  (636,20)  (636,11)  (636,7)  (631,7)  (631,14)  (630,11)  (630,68)  (630,48)  (630,29)  (630,21)  (630,7)  (630,7)  (626,7)  (626,14)  (625,23)  (625,7)  (624,22)  (624,7)  (624,7)  (622,19)  (622,10)  (622,6)  (609,4)  (606,5)  (602,7)  (598,8)  (598,15)  (597,12)  (597,73)  (597,53)  (597,34)  (597,21)  (597,8)  (597,8)  (593,8)  (593,15)  (592,24)  (592,8)  (591,23)  (591,8)  (591,8)  (589,20)  (589,11)  (589,7)  (582,7)  (582,14)  (581,11)  (581,54)  (581,40)  (581,27)  (581,7)  (581,7)  (577,7)  (577,14)  (576,23)  (576,7)  (575,22)  (575,7)  (575,7)  (573,19)  (573,10)  (573,6)  (514,4)  (536,12)  (536,57)  (536,42)  (536,28)  (536,20)  (536,8)  (533,13)  (533,83)  (533,68)  (533,48)  (533,29)  (533,21)  (533,9)  (530,14)  (530,44)  (530,30)  (530,22)  (530,10)  (528,14)  (528,44)  (528,30)  (528,22)  (528,10)  (527,24)  (527,13)  (527,13)  (527,9)  (525,23)  (525,12)  (525,8)  (524,22)  (524,11)  (524,7)  (520,12)  (520,42)  (520,28)  (520,20)  (520,8)  (519,11)  (519,11)  (519,7)  (517,19)  (517,10)  (517,6)  (516,20)  (516,9)  (516,5)  (514,8)  (514,24)  (514,21)  (485,4)  (505,12)  (505,57)  (505,48)  (505,34)  (505,21)  (505,8)  (503,13)  (503,83)  (503,74)  (503,54)  (503,35)  (503,22)  (503,9)  (501,14)  (501,50)  (501,36)  (501,23)  (501,10)  (499,14)  (499,50)  (499,36)  (499,23)  (499,10)  (498,24)  (498,13)  (498,13)  (498,9)  (497,23)  (497,12)  (497,8)  (496,22)  (496,11)  (496,7)  (491,12)  (491,48)  (491,34)  (491,21)  (491,8)  (490,11)  (490,11)  (490,7)  (488,19)  (488,10)  (488,6)  (487,20)  (487,9)  (487,5)  (485,8)  (485,25)  (485,22)  (451,4)  (471,12)  (471,57)  (471,48)  (471,34)  (471,21)  (471,8)  (469,13)  (469,83)  (469,74)  (469,54)  (469,35)  (469,22)  (469,9)  (467,14)  (467,50)  (467,36)  (467,23)  (467,10)  (465,14)  (465,50)  (465,36)  (465,23)  (465,10)  (464,24)  (464,13)  (464,13)  (464,9)  (463,23)  (463,12)  (463,8)  (462,22)  (462,11)  (462,7)  (458,12)  (458,48)  (458,34)  (458,21)  (458,8)  (457,11)  (457,11)  (457,7)  (455,19)  (455,10)  (455,6)  (453,20)  (453,9)  (453,5)  (451,8)  (451,25)  (451,22)  (423,3)  (423,10)  (420,4)  (420,11)  (414,6)  (414,13)  (413,10)  (413,55)  (413,40)  (413,26)  (413,18)  (413,6)  (413,6)  (408,7)  (408,14)  (407,11)  (407,81)  (407,66)  (407,46)  (407,27)  (407,19)  (407,7)  (407,7)  (403,8)  (403,15)  (402,12)  (402,42)  (402,28)  (402,20)  (402,8)  (402,8)  (398,8)  (398,15)  (397,12)  (397,42)  (397,28)  (397,20)  (397,8)  (397,8)  (395,22)  (395,11)  (395,11)  (395,7)  (394,21)  (394,10)  (394,6)  (392,20)  (392,9)  (392,5)  (388,6)  (388,13)  (385,48)  (385,55)  (384,10)  (384,40)  (384,26)  (384,18)  (384,6)  (384,6)  (382,9)  (382,9)  (382,5)  (380,17)  (380,8)  (380,4)  (378,18)  (378,7)  (378,3)  (376,6)  (376,22)  (376,19)  (320,23)  (320,51)  (320,42)  (320,34)  (320,17) )

Total verification time: 7.46 second(s)
	Time spent in main process: 3.65 second(s)
	Time spent in child processes: 3.81 second(s)
