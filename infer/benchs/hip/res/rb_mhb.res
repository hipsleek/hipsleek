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
                              EXISTS(flted_43_4165,flted_43_4166,
                              S5_4167: res::rb1<flted_43_4166,flted_43_4165,S5_4167>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S5_4167=union(S1,S2,{0},S3,S4,{0},{0})]
                               [-1+flted_43_4165=bha & 1<=bha]
                               [0=flted_43_4166][1<=bha_493]
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
                              EXISTS(flted_83_4286,flted_83_4287,
                              S5_4288: res::rb1<flted_83_4287,flted_83_4286,S5_4288>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S5_4288=union(S1,S2,S3,S4,{0},{0},{0})]
                               [-1+flted_83_4286=bha & 1<=bha]
                               [0=flted_83_4287][1<=bha_437]
                               [0<=flted_82_431 & flted_82_431<=1]
                               [1<=bha_436]
                               [0<=flted_82_432 & flted_82_432<=1]
                               [1<=bha_435]
                               [0<=flted_82_433 & flted_82_433<=1]
                               [0<=flted_82_434 & flted_82_434<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S3_4191:exists(v_4218:exists(S4_4279:exists(S1_4188:exists(S2_4189:exists(S2_4224:exists(S1_4221:v_4218=0 & 
  S4_4279=union(S1_4188,S2_4189,S3_4191,{0},{0}) & S3_4191=union(S1_4221,
  S2_4224,{v_4218}) & S4_4279=S5 & S1=S1_4188 & S2_4189=S2 & S4=S2_4224 & 
  S3=S1_4221)))))))) --> ROT2R(S5,S1,S2,S3,S4)]
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
                   (failure_code=213)  S2_4791=S & S2_4791=S3_4939 & S1_4787=S_4869 & S1_4787=S2_4938 & 
S4_5267=union(S1_4937,S2_4938,S3_4939,{0},{0}) & v_int_321_5268=0 & 
S1_5277=S4_5267 & S1_4937=S1 & S2=union(S1_4787,S2_4791,{v_4783}) & S2!=() & 
S3=S2_5281 & S3!=() & v_int_321_5268=v_5273 |-  union(S1,S2,S3,{0},{0})=union(S1_5277,S2_5281,{v_5273}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(575::,1 ); (575::,1 ); (569::,0 ); (569::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S1_5060=S2_5092 & S2_5063=S3_5093 & S_4869!=() & S_4869=union(S1_5060,
S2_5063,{v_5057}) & S_4869=S1_4787 & S=S2_4791 & S=S4 & 
S5_5340=union(S1_5091,S2_5092,S3_5093,S4,{0},{0},{0}) & v_int_321_5343=0 & 
S3=S2_5356 & S3!=() & S1_5352=S5_5340 & S1=S1_5091 & S2!=() & 
S2=union(S1_4787,S2_4791,{v_4783}) & v_int_321_5343=v_5348 |-  union(S1,S2,S3,{0},{0})=union(S1_5352,S2_5356,{v_5348}) (may-bug).
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
                   (failure_code=213)  v_int_344_7543=0 & S2_6694=S_6772 & S2_6694=S2_6841 & S1_6690=S & 
S1_6690=S1_6840 & S4_7542=union(S1_6840,S2_6841,S3_6842,{0},{0}) & 
v_int_344_7543=v_7548 & S1=S1_7552 & S1!=() & S2_7556=S4_7542 & S3_6842=S3 & 
S2=union(S1_6690,S2_6694,{v_6686}) & S2!=() |-  union(S1,S2,S3,{0},{0})=union(S1_7552,S2_7556,{v_7548}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(550::,1 ); (550::,1 ); (545::,0 ); (545::,0 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  S1_6970=S2_6998 & S2_6973=S3_6999 & S_6772!=() & S_6772=union(S1_6970,
S2_6973,{v_6967}) & v_int_344_7618=0 & S_6772=S2_6694 & S=S1_6690 & 
S=S1_6997 & S5_7615=union(S1_6997,S2_6998,S3_6999,S4,{0},{0},{0}) & 
v_int_344_7618=v_7623 & S2_7631=S5_7615 & S3=S4 & S2=union(S1_6690,S2_6694,
{v_6686}) & S2!=() & S1=S1_7627 & S1!=() |-  union(S1,S2,S3,{0},{0})=union(S1_7627,S2_7631,{v_7623}) (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}};
 Label: [(545::,1 ); (545::,1 )]
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: 
                   (failure_code=213)  v_int_344_7693=0 & S1_7140=S1_6690 & S1_7140=S & S2_6694=S2_7141 & 
S1_6690!=() & S4_7690=union(S1_7140,S2_7141,S3_7142,{0},{0}) & 
v_int_344_7693=v_7698 & S1=S1_7702 & S1!=() & S2_7706=S4_7690 & S3=S3_7142 & 
S2=union(S1_6690,S2_6694,{v_6686}) & S2!=() |-  union(S1,S2,S3,{0},{0})=union(S1_7702,S2_7706,{v_7698}) (may-bug).
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
                              EXISTS(flted_271_12502,flted_271_12503,
                              S4_12504: res::rb1<flted_271_12503,flted_271_12502,S4_12504>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12504=union(S1,S2,S3,{0},{0})]
                               [-1+flted_271_12502=ha & 1<=ha]
                               [0=flted_271_12503][1<=ha_212]
                               [0<=flted_270_208 & flted_270_208<=1]
                               [1<=ha_211]
                               [0<=flted_270_209 & flted_270_209<=1]
                               [0<=flted_270_210 & flted_270_210<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12443:exists(S2_12449:exists(S1_12446:exists(S1_12421:exists(S2_12425:exists(v_12417:v_12443=0 & 
  S2_12425=union(S1_12446,S2_12449,{v_12443}) & v_12417=0 & S1_12421=S1 & 
  S3=S2_12449 & S2=S1_12446 & S4=union(S1_12421,S2_12425,
  {v_12417})))))))) --> DEL3(S1,S2,S3,S4)]
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
                              EXISTS(flted_289_12640,flted_289_12641,
                              S4_12642: res::rb1<flted_289_12641,flted_289_12640,S4_12642>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12642=union(S1,S2,{0},S3,{0})]
                               [-1+flted_289_12640=ha & 1<=ha]
                               [0=flted_289_12641][1<=ha_187]
                               [0<=flted_288_183 & flted_288_183<=1]
                               [1<=ha_186]
                               [0<=flted_288_184 & flted_288_184<=1]
                               [0<=flted_288_185 & flted_288_185<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12581:exists(S2_12587:exists(S1_12584:exists(S1_12559:exists(S2_12563:exists(v_12555:v_12581=0 & 
  S1_12559=union(S1_12584,S2_12587,{v_12581}) & v_12555=0 & S3=S2_12563 & 
  S2=S2_12587 & S1=S1_12584 & S4=union(S1_12559,S2_12563,
  {v_12555})))))))) --> DEL3R(S1,S2,S3,S4)]
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
                              EXISTS(flted_231_12778,flted_231_12779,
                              S4_12780: res::rb1<flted_231_12779,flted_231_12778,S4_12780>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12780=union(S1,S2,S3,{0},{0})]
                               [-1+flted_231_12778=ha & 1<=ha]
                               [0=flted_231_12779][1<=ha_262]
                               [0<=flted_230_258 & flted_230_258<=1]
                               [1<=ha_261]
                               [0<=flted_230_259 & flted_230_259<=1]
                               [0<=flted_230_260 & flted_230_260<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12719:exists(S2_12725:exists(S1_12722:exists(S1_12697:exists(S2_12701:exists(v_12693:v_12719=0 & 
  S2_12701=union(S1_12722,S2_12725,{v_12719}) & v_12693=0 & S1_12697=S1 & 
  S3=S2_12725 & S2=S1_12722 & S4=union(S1_12697,S2_12701,
  {v_12693})))))))) --> DEL4(S1,S2,S3,S4)]
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
                              EXISTS(flted_249_12916,flted_249_12917,
                              S4_12918: res::rb1<flted_249_12917,flted_249_12916,S4_12918>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S4_12918=union(S1,S2,{0},S3,{0})]
                               [-1+flted_249_12916=ha & 1<=ha]
                               [0=flted_249_12917][1<=ha_237]
                               [0<=flted_248_233 & flted_248_233<=1]
                               [1<=ha_236]
                               [0<=flted_248_234 & flted_248_234<=1]
                               [0<=flted_248_235 & flted_248_235<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_12857:exists(S2_12863:exists(S1_12860:exists(S1_12835:exists(S2_12839:exists(v_12831:v_12857=0 & 
  S1_12835=union(S1_12860,S2_12863,{v_12857}) & v_12831=0 & S3=S2_12839 & 
  S2=S2_12863 & S1=S1_12860 & S4=union(S1_12835,S2_12839,
  {v_12831})))))))) --> DEL4R(S1,S2,S3,S4)]
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
                              
                              EXISTS(flted_160_13647,flted_160_13648,
                              S4_13649: res::rb1<flted_160_13648,flted_160_13647,S4_13649>@M[Orig][LHSCase]@ rem br[{694}]&
                              (
                              ([S3!=()][null!=res][color=0][S4_13649!=()]
                               [(0<=flted_158_380 & flted_158_380<=1 & 
                                 1<=h & 0<=Anon_13 & Anon_13<=1 & 1<=h_383 & 
                                 0<=flted_158_379 & flted_158_379<=1 & 
                                 1<=h_384 | 0<=flted_159_382 & 
                                 flted_159_382<=1 & 1<=h & 0<=Anon_14 & 
                                 Anon_14<=1 & 1<=h_385 & 0<=flted_159_381 & 
                                 flted_159_381<=1 & 1<=h_386) & -2+
                                 flted_160_13647=h]
                               [0=flted_160_13648]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(flted_161_13650,flted_161_13651,
                                 S5_13652: res::rb1<flted_161_13651,flted_161_13650,S5_13652>@M[Orig][LHSCase]@ rem br[{695}]&
                                 (
                                 ([S3!=()][null!=res][color=1][S5_13652!=()]
                                  [(0<=flted_158_380 & flted_158_380<=1 & 
                                    1<=h & 0<=Anon_13 & Anon_13<=1 & 
                                    1<=h_383 & 0<=flted_158_379 & 
                                    flted_158_379<=1 & 1<=h_384 | 
                                    0<=flted_159_382 & flted_159_382<=1 & 
                                    1<=h & 0<=Anon_14 & Anon_14<=1 & 
                                    1<=h_385 & 0<=flted_159_381 & 
                                    flted_159_381<=1 & 1<=h_386) & -1+
                                    flted_161_13650=h]
                                  [1=flted_161_13651]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (exists(v_13113:exists(S2_13172:exists(v_13164:exists(S1_13168:exists(S2_13121:exists(S1_13117:exists(S1_13101:exists(S2_13105:exists(v_13097:exists(S1_13021:exists(S2_13024:exists(v_13018:v_13113=0 & 
  S2_13105=union(S1_13168,S2_13172,{v_13164}) & S1_13101=union(S1_13117,
  S2_13121,{v_13113}) & S2_13172=S2_13024 & v_13164=v_13018 & 
  S1_13021=S1_13168 & v_13097=0 & S2=S2_13121 & S1=S1_13117 & 
  S4=union(S1_13101,S2_13105,{v_13097}) & S3!=() & S3=union(S1_13021,
  S2_13024,{v_13018})))))))))))))) --> DEL61(S1,S2,S3,S4),
 (exists(v_13570:exists(S2_13605:exists(v_13597:exists(S1_13601:exists(S2_13578:exists(S1_13574:exists(S1_13555:exists(S2_13558:exists(v_13552:exists(S1_13045:exists(S2_13048:exists(v_13042:v_13570=0 & 
  S2_13558=union(S1_13601,S2_13605,{v_13597}) & S1_13555=union(S1_13574,
  S2_13578,{v_13570}) & S2_13605=S2_13048 & v_13597=v_13042 & 
  S1_13045=S1_13601 & v_13552=0 & S2=S2_13578 & S1=S1_13574 & 
  S5=union(S1_13555,S2_13558,{v_13552}) & S3!=() & S3=union(S1_13045,
  S2_13048,{v_13042})))))))))))))) --> DEL62(S1,S2,S3,S5)]
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
                              EXISTS(Anon_14648,bh1_14649,
                              S1_14650: res::rb1<Anon_14648,bh1_14649,S1_14650>@M[Orig][LHSCase]@ rem br[{695,694}]&
                              (
                              ([forall(_x:_x <notin> S1_14650  | _x=v) & 
                                 S1_14650!=() & S1_14650={v}]
                               [S=][bh1_14649<=bh & 1<=bh & bh<=bh1_14649]
                               [null!=res][Anon_20<=1 & 0<=Anon_20]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(S1_14609:exists(S2_14612:exists(v_14606:S1_14609= & S2_14612= & 
  v_14606=v & S= & S1=union(S1_14609,S2_14612,{v_14606}))))) --> INS(S1,S,v)]
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
                              
                              EXISTS(cl_14920,bh_14921,
                              S1_14922: x::rb1<cl_14920,bh_14921,S1_14922>@M[Orig][LHSCase]@ rem br[{695}]&
                              (
                              ([S=S1_14922 & S1_14922!=()][null!=x]
                               [bh=bh_14921 & 1<=bh]
                               [1=cl & 1=cl_14920 & 0<=cl & cl<=1][!(res)]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_14923,bh_14924,
                                 S2_14925: x::rb1<cl_14923,bh_14924,S2_14925>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                 (
                                 ([S=S2_14925][bh=bh_14924 & 1<=bh]
                                  [0=cl & 0=cl_14923 & 0<=cl & cl<=1][
                                  res]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S=S2) --> BLACK2(S2,S),
 (S=S2 & S2=) --> BLACK2(S2,S),
 (exists(S1_14810:exists(S2_14814:exists(v_14806:exists(S1_14741:exists(S2_14745:exists(v_14737:S1_14810=S1_14741 & 
  v_14737=v_14806 & S2_14745=S2_14814 & S2=union(S1_14810,S2_14814,
  {v_14806}) & S!=() & S=union(S1_14741,S2_14745,
  {v_14737})))))))) --> BLACK2(S2,S),
 (exists(S1_14721:exists(S2_14724:exists(v_14718:exists(S1_14853:exists(S2_14856:exists(v_14850:S1_14853=S1_14721 & 
  v_14718=v_14850 & S2_14724=S2_14856 & S!=() & S=union(S1_14721,S2_14724,
  {v_14718}) & S1=union(S1_14853,S2_14856,{v_14850})))))))) --> BLACK1(S1,S)]
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
                              
                              EXISTS(cl_15195,bh_15196,
                              S1_15197: x::rb1<cl_15195,bh_15196,S1_15197>@M[Orig][LHSCase]@ rem br[{695}]&
                              (
                              ([S=S1_15197 & S1_15197!=()][null!=x]
                               [bh=bh_15196 & 1<=bh]
                               [1=cl & 1=cl_15195 & 0<=cl & cl<=1][res]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(cl_15198,bh_15199,
                                 S2_15200: x::rb1<cl_15198,bh_15199,S2_15200>@M[Orig][LHSCase]@ rem br[{696,694}]&
                                 (
                                 ([S=S2_15200][bh=bh_15199 & 1<=bh]
                                  [0=cl & 0=cl_15198 & 0<=cl & cl<=1][
                                  !(res)]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[ (S2= & S=S2) --> RED2(S2,S),
 (S=S2 & S2=) --> RED2(S2,S),
 (exists(S1_15085:exists(S2_15089:exists(v_15081:exists(S1_15016:exists(S2_15020:exists(v_15012:S1_15085=S1_15016 & 
  v_15012=v_15081 & S2_15020=S2_15089 & S2=union(S1_15085,S2_15089,
  {v_15081}) & S!=() & S=union(S1_15016,S2_15020,
  {v_15012})))))))) --> RED2(S2,S),
 (exists(S1_14996:exists(S2_14999:exists(v_14993:exists(S1_15128:exists(S2_15131:exists(v_15125:S1_15128=S1_14996 & 
  v_14993=v_15125 & S2_14999=S2_15131 & S!=() & S=union(S1_14996,S2_14999,
  {v_14993}) & S1=union(S1_15128,S2_15131,{v_15125})))))))) --> RED1(S1,S)]
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
                              EXISTS(flted_21_15336,flted_21_15337,
                              S4_15338: res::rb1<flted_21_15337,flted_21_15336,S4_15338>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S1!=() & S4_15338=union(S1,S2,S3,{0},{0})]
                               [-1+flted_21_15336=bha & 1<=bha]
                               [0=flted_21_15337][1<=bha_518]
                               [0<=flted_20_514 & flted_20_514<=1]
                               [1<=bha_517]
                               [0<=flted_20_515 & flted_20_515<=1]
                               [0<=flted_20_516 & flted_20_516<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_15277:exists(S2_15283:exists(S1_15280:exists(S1_15255:exists(S2_15259:exists(v_15251:v_15277=0 & 
  S2_15259=union(S1_15280,S2_15283,{v_15277}) & v_15251=0 & S1_15255=S1 & 
  S3=S2_15283 & S2=S1_15280 & S1!=() & S4=union(S1_15255,S2_15259,
  {v_15251})))))))) --> ROT3(S4,S1,S2,S3)]
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
                              EXISTS(flted_63_15474,flted_63_15475,
                              S4_15476: res::rb1<flted_63_15475,flted_63_15474,S4_15476>@M[Orig][LHSCase]@ rem br[{696,694}]&
                              (
                              ([S3!=() & S4_15476=union(S1,S2,{0},S3,{0})]
                               [-1+flted_63_15474=bha & 1<=bha]
                               [0=flted_63_15475][1<=bha_462]
                               [0<=flted_62_458 & flted_62_458<=1]
                               [1<=bha_461]
                               [0<=flted_62_459 & flted_62_459<=1]
                               [0<=flted_62_460 & flted_62_460<=1]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_15415:exists(S2_15421:exists(S1_15418:exists(S1_15393:exists(S2_15397:exists(v_15389:v_15415=0 & 
  S1_15393=union(S1_15418,S2_15421,{v_15415}) & v_15389=0 & S2_15397=S3 & 
  S2=S2_15421 & S1=S1_15418 & S3!=() & S4=union(S1_15393,S2_15397,
  {v_15389})))))))) --> ROT3R(S4,S1,S2,S3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_case_3r$node~node~node SUCCESS

Termination checking result:


309 false contexts at: ( (655,4)  (652,5)  (648,7)  (645,8)  (645,15)  (644,12)  (644,51)  (644,37)  (644,29)  (644,8)  (644,8)  (640,8)  (640,15)  (639,24)  (639,8)  (638,23)  (638,8)  (638,8)  (636,20)  (636,11)  (636,7)  (631,7)  (631,14)  (630,11)  (630,68)  (630,48)  (630,29)  (630,21)  (630,7)  (630,7)  (626,7)  (626,14)  (625,23)  (625,7)  (624,22)  (624,7)  (624,7)  (622,19)  (622,10)  (622,6)  (609,4)  (606,5)  (602,7)  (598,8)  (598,15)  (597,12)  (597,73)  (597,53)  (597,34)  (597,21)  (597,8)  (597,8)  (593,8)  (593,15)  (592,24)  (592,8)  (591,23)  (591,8)  (591,8)  (589,20)  (589,11)  (589,7)  (582,7)  (582,14)  (581,11)  (581,54)  (581,40)  (581,27)  (581,7)  (581,7)  (577,7)  (577,14)  (576,23)  (576,7)  (575,22)  (575,7)  (575,7)  (573,19)  (573,10)  (573,6)  (514,4)  (536,12)  (536,57)  (536,42)  (536,28)  (536,20)  (536,8)  (533,13)  (533,83)  (533,68)  (533,48)  (533,29)  (533,21)  (533,9)  (530,14)  (530,44)  (530,30)  (530,22)  (530,10)  (528,14)  (528,44)  (528,30)  (528,22)  (528,10)  (527,24)  (527,13)  (527,13)  (527,9)  (525,23)  (525,12)  (525,8)  (524,22)  (524,11)  (524,7)  (520,12)  (520,42)  (520,28)  (520,20)  (520,8)  (519,11)  (519,11)  (519,7)  (517,19)  (517,10)  (517,6)  (516,20)  (516,9)  (516,5)  (514,8)  (514,24)  (514,21)  (485,4)  (505,12)  (505,57)  (505,48)  (505,34)  (505,21)  (505,8)  (503,13)  (503,83)  (503,74)  (503,54)  (503,35)  (503,22)  (503,9)  (501,14)  (501,50)  (501,36)  (501,23)  (501,10)  (499,14)  (499,50)  (499,36)  (499,23)  (499,10)  (498,24)  (498,13)  (498,13)  (498,9)  (497,23)  (497,12)  (497,8)  (496,22)  (496,11)  (496,7)  (491,12)  (491,48)  (491,34)  (491,21)  (491,8)  (490,11)  (490,11)  (490,7)  (488,19)  (488,10)  (488,6)  (487,20)  (487,9)  (487,5)  (485,8)  (485,25)  (485,22)  (451,4)  (471,12)  (471,57)  (471,48)  (471,34)  (471,21)  (471,8)  (469,13)  (469,83)  (469,74)  (469,54)  (469,35)  (469,22)  (469,9)  (467,14)  (467,50)  (467,36)  (467,23)  (467,10)  (465,14)  (465,50)  (465,36)  (465,23)  (465,10)  (464,24)  (464,13)  (464,13)  (464,9)  (463,23)  (463,12)  (463,8)  (462,22)  (462,11)  (462,7)  (458,12)  (458,48)  (458,34)  (458,21)  (458,8)  (457,11)  (457,11)  (457,7)  (455,19)  (455,10)  (455,6)  (453,20)  (453,9)  (453,5)  (451,8)  (451,25)  (451,22)  (423,3)  (423,10)  (420,4)  (420,11)  (414,6)  (414,13)  (413,10)  (413,55)  (413,40)  (413,26)  (413,18)  (413,6)  (413,6)  (408,7)  (408,14)  (407,11)  (407,81)  (407,66)  (407,46)  (407,27)  (407,19)  (407,7)  (407,7)  (403,8)  (403,15)  (402,12)  (402,42)  (402,28)  (402,20)  (402,8)  (402,8)  (398,8)  (398,15)  (397,12)  (397,42)  (397,28)  (397,20)  (397,8)  (397,8)  (395,22)  (395,11)  (395,11)  (395,7)  (394,21)  (394,10)  (394,6)  (392,20)  (392,9)  (392,5)  (388,6)  (388,13)  (385,48)  (385,55)  (384,10)  (384,40)  (384,26)  (384,18)  (384,6)  (384,6)  (382,9)  (382,9)  (382,5)  (380,17)  (380,8)  (380,4)  (378,18)  (378,7)  (378,3)  (376,6)  (376,22)  (376,19)  (320,23)  (320,51)  (320,42)  (320,34)  (320,17) )

Total verification time: 10.76 second(s)
	Time spent in main process: 5.02 second(s)
	Time spent in child processes: 5.74 second(s)
