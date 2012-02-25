/usr/local/bin/mona

Processing file "dll_msb.ss"
Parsing dll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure append$node~node... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(Anon_41,t,
                                S: res::dll<Anon_41,t,S>@M[Orig][LHSCase]&
                                t=n+m & APP(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              res::dll<Anon_41,t,S>@M[Orig][LHSCase]&t=n+m & 
                              S=union(S1,S2) & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2019:exists(v_2018:(S2= | S2=union(S1_2019,{v_2018})) & S1= & 
  S2=S))) --> APP(S,S1,S2),
 (exists(S1_2117:exists(v_2116:exists(S1_1829:exists(v_1827:exists(v_2035:exists(S1_2037:exists(S1_1984:exists(S1_2054:exists(v_1982:exists(v_2052:(S1_1984= | 
  S1_1984=union(S1_2117,{v_2116})) & S=union(S1_2037,{v_2035}) & 
  S1=union(S1_1829,{v_1827}) & APP(S_1922,S1_1835,S2_1838) & S2=S2_1838 & 
  S1_1829=S1_1835 & v_1827=v_2035 & S_1922=union(S1_1984,{v_1982}) & 
  S1_2037=union(S1_2054,{v_2052}) & S1_2037=union(S1_2054,{v_2052}) & 
  S1_1984=S1_2054 & v_1982=v_2052))))))))))) --> APP(S,S1,S2),
 (exists(S1_1829:exists(v_1827:exists(S1_2139:exists(v_2137:S1_2139= & 
  S1_2139= & S_1910= & v_1827=v_2137 & S1_1829=S1_1835 & S2=S2_1838 & 
  APP(S_1910,S1_1835,S2_1838) & S1=union(S1_1829,{v_1827}) & S=union(S1_2139,
  {v_2137})))))) --> APP(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure append1$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP1(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP1]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(Anon_42,t,
                                S: res::dll<Anon_42,t,S>@M[Orig][LHSCase]&
                                t=n+m & APP1(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              res::dll<Anon_42,t,S>@M[Orig][LHSCase]&t=n+m & 
                              S=union(S1,S2) & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2258:exists(v_2256:exists(v_2560:exists(S1_2562:S=union(S1_2562,
  {v_2560}) & S1=union(S1_2258,{v_2256}) & APP1(S_2339,S1_2264,S2_2267) & 
  S2=S2_2267 & S1_2258=S1_2264 & v_2256=v_2560 & S1_2562=S_2339 & S_2339= & 
  S1_2562= & S1_2562=))))) --> APP1(S,S1,S2),
 (exists(S1_2443:exists(v_2442:(S2= | S2=union(S1_2443,{v_2442})) & S1= & 
  S2=S))) --> APP1(S,S1,S2),
 (exists(S1_2540:exists(v_2539:exists(S1_2258:exists(v_2256:exists(v_2458:exists(S1_2460:exists(S1_2410:exists(S1_2477:exists(v_2408:exists(v_2475:(S1_2410= | 
  S1_2410=union(S1_2540,{v_2539})) & S=union(S1_2460,{v_2458}) & 
  S1=union(S1_2258,{v_2256}) & APP1(S_2351,S1_2264,S2_2267) & S2=S2_2267 & 
  S1_2258=S1_2264 & v_2256=v_2458 & S_2351=union(S1_2410,{v_2408}) & 
  S1_2460=union(S1_2477,{v_2475}) & S1_2460=union(S1_2477,{v_2475}) & 
  S1_2410=S1_2477 & v_2408=v_2475))))))))))) --> APP1(S,S1,S2),
 (exists(S1_2258:exists(v_2256:exists(S1_2562:exists(v_2560:S1_2562= & 
  S1_2562= & S_2339= & S1_2562=S_2339 & v_2256=v_2560 & S1_2258=S1_2264 & 
  S2=S2_2267 & APP1(S_2339,S1_2264,S2_2267) & S1=union(S1_2258,{v_2256}) & 
  S=union(S1_2562,{v_2560})))))) --> APP1(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append1$node~node SUCCESS

Checking procedure append2$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  APP2(S,S1,S2)
!!! POST:  S=union(S1,S2)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [APP2]
              EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                    S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                    y::dll<p,n,S2>@M[Orig][LHSCase]&1<=m&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                EXISTS(q_219,t,
                                S: x::dll<q_219,t,S>@M[Orig][LHSCase]&t=n+
                                m & APP2(S,S1,S2) & q_219=q&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; m; S1; p; n; 
                  S2](ex)x::dll<q,m,S1>@M[Orig][LHSCase] * 
                  y::dll<p,n,S2>@M[Orig][LHSCase]&1<=m&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 42::
                              x::dll<q_219,t,S>@M[Orig][LHSCase]&t=n+m & 
                              q_219=q & S=union(S1,S2) & 0<=m & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_2665:exists(v_2985:exists(S1_2667:exists(S1_2987:S=union(S1_2987,
  {v_2985}) & S1=union(S1_2667,{v_2665}) & S2= & S1_2987=S2 & 
  v_2665=v_2985 & S1_2667= & S1_2987= & S1_2987=))))) --> APP2(S,S1,S2),
 (exists(S1_2933:exists(v_2932:exists(v_2665:exists(v_2852:exists(v_2775:exists(S1_2777:exists(S1_2667:exists(S1_2854:exists(S1_2874:exists(v_2872:(S1_2777= | 
  S1_2777=union(S1_2933,{v_2932})) & S=union(S1_2854,{v_2852}) & 
  S1=union(S1_2667,{v_2665}) & S2=union(S1_2777,{v_2775}) & v_2665=v_2852 & 
  v_2775=v_2872 & S1_2777=S1_2874 & S1_2667= & S1_2854=union(S1_2874,
  {v_2872}) & S1_2854=union(S1_2874,{v_2872})))))))))))) --> APP2(S,S1,S2),
 (exists(S1_2667:exists(v_2665:exists(S1_2987:exists(v_2985:S1_2987= & 
  S1_2987= & S1_2667= & v_2665=v_2985 & S1_2987=S2 & S2= & S1=union(S1_2667,
  {v_2665}) & S=union(S1_2987,{v_2985})))))) --> APP2(S,S1,S2),
 (exists(S1_3140:exists(v_3139:exists(S1_2667:exists(v_2665:exists(S1_3091:exists(v_3089:S_3088=union(S1_3140,
  {v_3139}) & S_3088=S1_3091 & v_2665=v_3089 & S1_2667=S1_2786 & 
  S2=S2_2789 & APP2(S_3088,S1_2786,S2_2789) & S1=union(S1_2667,{v_2665}) & 
  S=union(S1_3091,{v_3089})))))))) --> APP2(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
!!! REL :  CL(S,v)
!!! POST:  forall(_x:_x <notin> S  | _x=v)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CL]
              EBase true&0<=n&{FLOW,(20,21)=__norm}
                      ECase case {
                             n=0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 81::
                                                         true&res=null&
                                                         {FLOW,(20,21)=__norm})
                             ;
                             0<n -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 82::
                                                         EXISTS(n_197,
                                                         Anon_67,
                                                         S: res::dll<Anon_67,n_197,S>@M[Orig][LHSCase]&
                                                         CL(S,v) & n_197=n&
                                                         {FLOW,(20,21)=__norm}))
                             ;
                             n<0 -> ((None,[]),EBase true&MayLoop&
                                                     {FLOW,(1,23)=__flow}
                                                       EAssume 83::
                                                         true&true&
                                                         {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase true&0<=n&{FLOW,(20,21)=__norm}
                    ECase case {
                           n=0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 81::
                                                       true&res=null & n=0&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           0<n -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 82::
                                                       res::dll<Anon_67,n_197,S>@M[Orig][LHSCase]&
                                                       n_197=n & 
                                                       forall(_x:_x <notin> S
                                                        | _x=v) & 0<n&
                                                       {FLOW,(20,21)=__norm})
                           ;
                           n<0 -> ((None,[]),EBase true&MayLoop&
                                                   {FLOW,(1,23)=__flow}
                                                     EAssume 83::
                                                       true&n<0&
                                                       {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (exists(S1_3312:exists(v_3310:S1_3312= & S1_3312= & v=v_3310 & 
  S=union(S1_3312,{v_3310})))) --> CL(S,v),
 (exists(S1_3408:exists(v_3407:exists(v_3330:exists(S1_3332:exists(S1_3307:exists(S1_3349:exists(v_3305:exists(v_3347:(S1_3307= | 
  S1_3307=union(S1_3408,{v_3407})) & S=union(S1_3332,{v_3330}) & 
  CL(S_3250,v) & v=v_3330 & S_3250=union(S1_3307,{v_3305}) & 
  S1_3332=union(S1_3349,{v_3347}) & S1_3332=union(S1_3349,{v_3347}) & 
  S1_3307=S1_3349 & v_3305=v_3347))))))))) --> CL(S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_34; m; 
                    S3](ex)x::dll<Anon_34,m,S3>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 16::ref [x]
                                EXISTS(n_230,Anon_35,
                                S4: x'::dll<Anon_35,n_230,S4>@M[Orig][LHSCase]&
                                n_230=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_34; m; 
                  S3](ex)x::dll<Anon_34,m,S3>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 16::ref [x]
                              
                              x::dll<Anon_34,m,S3>@M[Orig][LHSCase] * 
                              x'::dll<Anon_35,n_230,S4>@M[Orig][LHSCase]&
                              n_230=0 & n=0 & x'=null & S4= & 0<=m&
                              {FLOW,(20,21)=__norm}
                              or x::dll<Anon_34,m,S3>@M[Orig][LHSCase] * 
                                 x'::dll<Anon_35,n_230,S4>@M[Orig][LHSCase]&
                                 Anon_67_3482=Anon_35 & S_3484=S4 & 
                                 n_230=n_197_3483 & n=n_197_3483 & 
                                 1<=n_197_3483 & 
                                 907::forall(_x:_x <notin> S_3484  | _x=v) & 
                                 0<=m&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

!!! REL :  DEL(S,S1)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&a<n & 0<a&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::
                                EXISTS(p_202,m,
                                S1: x::dll<p_202,m,S1>@M[Orig][LHSCase]&
                                DEL(S,S1) & p_202=p&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&1<=a & a<n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 66::
                              x::dll<p_202,m,S1>@M[Orig][LHSCase]&p_202=p & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_3839:exists(v_3838:exists(v_3531:exists(v_3758:exists(S1_3533:exists(v_3573:exists(S1_3760:exists(S1_3575:exists(S1_3659:exists(S1_3777:exists(v_3657:exists(v_3775:(S1_3659= | 
  S1_3659=union(S1_3839,{v_3838})) & S1=union(S1_3760,{v_3758}) & 
  S=union(S1_3533,{v_3531}) & v_3531=v_3758 & S1_3533=union(S1_3575,
  {v_3573}) & S1_3760=union(S1_3777,{v_3775}) & S1_3760=union(S1_3777,
  {v_3775}) & S1_3575=union(S1_3659,{v_3657}) & S1_3659=S1_3777 & 
  v_3657=v_3775))))))))))))) --> DEL(S,S1),
 (exists(S1_3575:exists(v_3573:exists(S1_3533:exists(v_3531:exists(S1_3847:exists(v_3845:S1_3575= & 
  S1_3847= & S1_3847= & S1_3533=union(S1_3575,{v_3573}) & v_3531=v_3845 & 
  S=union(S1_3533,{v_3531}) & S1=union(S1_3847,{v_3845})))))))) --> DEL(S,S1),
 (exists(S1_3922:exists(v_3921:exists(S1_3706:exists(v_3704:exists(v_3877:exists(S1_3879:(S1_3875= | 
  S1_3875=union(S1_3922,{v_3921})) & S1=union(S1_3879,{v_3877}) & 
  S=union(S1_3706,{v_3704}) & DEL(S_3721,S1_3875) & S1_3706=S_3721 & 
  v_3704=v_3877 & S1_3875=S1_3879))))))) --> DEL(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...
Timeout when checking #simplify  Restarting Omega after ... 147 invocations Stop Omega... 147 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 148 invocations Stop Omega... 148 invocations Starting Omega...oc

Context of Verification Failure: File "dll_msb.ss",Line:302,Col:10
Last Proving Location: File "dll_msb.ss",Line:319,Col:8

ERROR: at _0_0 
Message: Unexpected error in computing fixpoint by FixBag
 
!!! IGNORING PROBLEM of fix-point calculation
!!! OLD SPECS: ((None,[]),EInfer [DEL2]
              EBase exists (Expl)(Impl)[Anon_65; n; 
                    S](ex)x::dll<Anon_65,n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 74::ref [x]
                                EXISTS(Anon_66,m,
                                S1: res::dll<Anon_66,m,S1>@M[Orig][LHSCase]&
                                m<=n & DEL2(a,S,S1)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_65; n; 
                  S](ex)x::dll<Anon_65,n,S>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 74::ref [x]
                              EXISTS(Anon_4571,m_4572,
                              S1_4573: res::dll<Anon_4571,m_4572,S1_4573>@M[Orig][LHSCase]&
                              m_4572<=n & DEL2(a,S,S1_4573) & 0<=n&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (S1= & S= & S1=S) --> DEL2(a,S,S1),
 (exists(v_3989:exists(S1_3991:S1= & S=union(S1_3991,{v_3989}) & 
  S1=S1_3991 & a=v_3989 & S1_3991=))) --> DEL2(a,S,S1),
 (exists(Anon_65:exists(p_3986:exists(x':exists(Anon_4098:exists(self_3987:exists(flted_12_3988:exists(n_4099:exists(res:exists(v_node_320_1166':exists(nn_200':exists(self_4429:exists(Anon_4143:exists(m_4144:exists(flted_12_4430:exists(Anon_66:exists(m:exists(v_bool_318_1165':exists(v_bool_304_1168':exists(v_bool_308_1167':exists(v_null_317_4156:exists(q_4416:exists(x:exists(nn2_201':exists(n:exists(v_4415:exists(S1_3991:exists(v_3989:exists(S1_4417:(Anon_65=p_3986 & 
  x'=x & Anon_4098=x & self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+
  n_4099=n & res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  nn_200'=q_4416 & self_4429=Anon_4143 & flted_12_4430=0 & S1_4417=S1_4145 & 
  m_4144=0 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & (1+a)<=v_4415 & !(v_bool_308_1167') & 
  v_null_317_4156=null & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145) | Anon_65=p_3986 & x'=x & Anon_4098=x & 
  self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  nn_200'=q_4416 & self_4429=Anon_4143 & flted_12_4430=0 & S1_4417=S1_4145 & 
  m_4144=0 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & !(v_bool_308_1167') & v_null_317_4156=null & (1+
  v_4415)<=a & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145) | Anon_65=p_3986 & x'=x & Anon_4098=x & 
  self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  self_4429=Anon_4143 & m_4144=0 & flted_12_4430=0 & S1_4417=S1_4145 & 
  nn_200'=q_4416 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & (1+a)<=v_4415 & !(v_bool_308_1167') & 
  v_null_317_4156=null & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145) | Anon_65=p_3986 & x'=x & Anon_4098=x & 
  self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  self_4429=Anon_4143 & m_4144=0 & flted_12_4430=0 & S1_4417=S1_4145 & 
  nn_200'=q_4416 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & !(v_bool_308_1167') & v_null_317_4156=null & (1+
  v_4415)<=a & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145) | (Anon_65=p_3986 & x'=x & Anon_4098=x & 
  self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  nn_200'=q_4416 & self_4429=Anon_4143 & m_4144=0 & flted_12_4430=0 & 
  S1_4417=S1_4145 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & (1+a)<=v_4415 & !(v_bool_308_1167') & 
  v_null_317_4156=null & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145) | Anon_65=p_3986 & x'=x & Anon_4098=x & 
  self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  nn_200'=q_4416 & self_4429=Anon_4143 & m_4144=0 & flted_12_4430=0 & 
  S1_4417=S1_4145 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & !(v_bool_308_1167') & (1+v_4415)<=a & 
  v_null_317_4156=null & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145)) & S1_4145=) & S1=union(S1_4417,{v_4415}) & 
  S=union(S1_3991,{v_3989}) & S1_4145= & S1_4417= & 
  S1_4417=))))))))))))))))))))))))))))) --> DEL2(a,S,S1),
 (S1=S & S= & S1=) --> DEL2(a,S,S1),
 (exists(S1_4295:exists(v_4294:exists(v_3989:exists(v_4239:exists(S1_4241:exists(S1_3991:exists(S1_4084:exists(v_4082:(S1_4084= | 
  S1_4084=union(S1_4295,{v_4294})) & S1=union(S1_4241,{v_4239}) & 
  S=union(S1_3991,{v_3989}) & a=v_3989 & v_4082=v_4239 & S1_4084=S1_4241 & 
  S1_3991=union(S1_4084,{v_4082})))))))))) --> DEL2(a,S,S1),
 (exists(S1_3991:exists(v_3989:S1_3991= & a=v_3989 & S1=S1_3991 & 
  S=union(S1_3991,{v_3989}) & S1=))) --> DEL2(a,S,S1),
 (exists(Anon_4143:exists(p_4215:exists(Anon_65:exists(p_3986:exists(x':exists(Anon_4098:exists(self_3987:exists(flted_12_3988:exists(m_4144:exists(n_4099:exists(res:exists(v_node_320_1166':exists(q_4320:exists(nn_200':exists(q_4219:exists(Anon_66:exists(flted_12_4217:exists(m:exists(flted_12_156_4393:exists(n:exists(v_bool_304_1168':exists(v_bool_308_1167':exists(v_null_317_4162:exists(x:exists(q_4337:exists(self_4216:exists(nn2_201':exists(v_bool_318_1165':exists(S1_4395:exists(v_4394:exists(v_4319:exists(S1_3991:exists(v_3989:exists(S1_4220:exists(v_4218:exists(S1_4321:exists(S1_4338:exists(v_4336:(S1_4220= & 
  (Anon_4143=p_4215 & Anon_65=p_3986 & x'=x & Anon_4098=x & self_3987=x & 
  S1_3991=S_4100 & 1+flted_12_3988=n & m_4144=1 & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4319 & 
  q_4320=self_4216 & nn_200'=self_4216 & v_4218=v_4336 & q_4219=q_4337 & 
  S1_4220=S1_4338 & Anon_66=v_null_317_4162 & flted_12_4217=0 & m=2 & 
  q_4337=null & !(v_bool_304_1168') & (1+a)<=v_4319 & !(v_bool_308_1167') & 
  v_null_317_4162=null & x!=null & self_4216!=null & nn2_201'!=null & 
  v_bool_318_1165' & 2<=n & DEL2(a,S_4100,S1_4145) | Anon_4143=p_4215 & 
  Anon_65=p_3986 & x'=x & Anon_4098=x & self_3987=x & S1_3991=S_4100 & 1+
  flted_12_3988=n & m_4144=1 & 1+n_4099=n & res=nn2_201' & 
  v_node_320_1166'=nn2_201' & v_3989=v_4319 & q_4320=self_4216 & 
  nn_200'=self_4216 & v_4218=v_4336 & q_4219=q_4337 & S1_4220=S1_4338 & 
  Anon_66=v_null_317_4162 & flted_12_4217=0 & m=2 & q_4337=null & 
  !(v_bool_304_1168') & !(v_bool_308_1167') & v_null_317_4162=null & (1+
  v_4319)<=a & x!=null & self_4216!=null & nn2_201'!=null & 
  v_bool_318_1165' & 2<=n & DEL2(a,S_4100,S1_4145)) | (Anon_4143=p_4215 & 
  Anon_65=p_3986 & x'=x & Anon_4098=x & self_3987=x & S1_3991=S_4100 & 1+
  flted_12_3988=n & -2+m_4144=flted_12_156_4393 & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4319 & 
  q_4320=self_4216 & nn_200'=self_4216 & v_4218=v_4336 & q_4219=q_4337 & 
  S1_4220=S1_4338 & Anon_66=v_null_317_4162 & -1+
  flted_12_4217=flted_12_156_4393 & -3+m=flted_12_156_4393 & 
  0<=flted_12_156_4393 & (3+flted_12_156_4393)<=n & !(v_bool_304_1168') & (1+
  a)<=v_4319 & !(v_bool_308_1167') & v_null_317_4162=null & x!=null & 
  q_4337!=null & self_4216!=null & nn2_201'!=null & v_bool_318_1165' & 
  DEL2(a,S_4100,S1_4145) | Anon_4143=p_4215 & Anon_65=p_3986 & x'=x & 
  Anon_4098=x & self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & -2+
  m_4144=flted_12_156_4393 & 1+n_4099=n & res=nn2_201' & 
  v_node_320_1166'=nn2_201' & v_3989=v_4319 & q_4320=self_4216 & 
  nn_200'=self_4216 & v_4218=v_4336 & q_4219=q_4337 & S1_4220=S1_4338 & 
  Anon_66=v_null_317_4162 & -1+flted_12_4217=flted_12_156_4393 & -3+
  m=flted_12_156_4393 & 0<=flted_12_156_4393 & (3+flted_12_156_4393)<=n & 
  !(v_bool_304_1168') & !(v_bool_308_1167') & v_null_317_4162=null & (1+
  v_4319)<=a & x!=null & q_4337!=null & self_4216!=null & nn2_201'!=null & 
  v_bool_318_1165' & DEL2(a,S_4100,S1_4145)) & S1_4220=union(S1_4395,
  {v_4394})) & S1=union(S1_4321,{v_4319}) & S=union(S1_3991,{v_3989}) & 
  S1_4145=union(S1_4220,{v_4218}) & S1_4321=union(S1_4338,{v_4336}) & 
  S1_4321=union(S1_4338,
  {v_4336})))))))))))))))))))))))))))))))))))))))) --> DEL2(a,S,S1),
 (exists(Anon_65:exists(p_3986:exists(x':exists(Anon_4098:exists(self_3987:exists(flted_12_3988:exists(n_4099:exists(res:exists(v_node_320_1166':exists(nn_200':exists(self_4429:exists(Anon_4143:exists(m_4144:exists(flted_12_4430:exists(Anon_66:exists(m:exists(v_bool_318_1165':exists(v_bool_304_1168':exists(v_bool_308_1167':exists(v_null_317_4156:exists(q_4416:exists(x:exists(nn2_201':exists(n:exists(S1_3991:exists(v_3989:exists(S1_4417:exists(v_4415:S1_4417= & 
  S1_4417= & S1_4145= & (Anon_65=p_3986 & x'=x & Anon_4098=x & self_3987=x & 
  S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & res=nn2_201' & 
  v_node_320_1166'=nn2_201' & v_3989=v_4415 & nn_200'=q_4416 & 
  self_4429=Anon_4143 & m_4144=0 & flted_12_4430=0 & S1_4417=S1_4145 & 
  Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & (1+a)<=v_4415 & !(v_bool_308_1167') & 
  v_null_317_4156=null & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145) | Anon_65=p_3986 & x'=x & Anon_4098=x & 
  self_3987=x & S1_3991=S_4100 & 1+flted_12_3988=n & 1+n_4099=n & 
  res=nn2_201' & v_node_320_1166'=nn2_201' & v_3989=v_4415 & 
  nn_200'=q_4416 & self_4429=Anon_4143 & m_4144=0 & flted_12_4430=0 & 
  S1_4417=S1_4145 & Anon_66=v_null_317_4156 & m=1 & !(v_bool_318_1165') & 
  !(v_bool_304_1168') & !(v_bool_308_1167') & (1+v_4415)<=a & 
  v_null_317_4156=null & q_4416=null & x!=null & nn2_201'!=null & 1<=n & 
  DEL2(a,S_4100,S1_4145)) & S=union(S1_3991,{v_3989}) & S1=union(S1_4417,
  {v_4415})))))))))))))))))))))))))))))) --> DEL2(a,S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[Anon_76; n; 
                    S](ex)x::dll<Anon_76,n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 140::
                                
                                true&res=null&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_77,Anon_78,
                                   m: res::node<m,Anon_77,Anon_78>@M[Orig]&
                                   v<m & FGE(S,m)&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_76; n; 
                  S](ex)x::dll<Anon_76,n,S>@M[Orig][LHSCase]&0<=n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 140::
                              
                              true&res=null & 0<=n&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_77,Anon_78>@M[Orig]&v<m & 
                                 {m}<subset> S  & 0<=n&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(S1_4828:exists(v_4827:exists(S1_4733:exists(v:exists(v_4731:(S1_4733= | 
  S1_4733=union(S1_4828,{v_4827})) & S=union(S1_4733,{v_4731}) & (1+v)<=m & 
  v_4731=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_4733:exists(v_4731:v_4731<=v & S1_4733=S_4783 & 
  m_4842=m & (1+v)<=m & FGE(S_4783,m_4842) & S=union(S1_4733,
  {v_4731}))))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[Anon_45; n; 
                    S](ex)x::dll<Anon_45,n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::ref [x]
                                EXISTS(flted_207_215,flted_207_216,Anon_46,
                                Anon_47,S1,
                                S2: x'::dll<Anon_46,flted_207_216,S1>@M[Orig][LHSCase] * 
                                res::dll<Anon_47,flted_207_215,S2>@M[Orig][LHSCase]&
                                flted_207_216=1 & flted_207_215+1=n & 
                                GN(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_45; n; 
                  S](ex)x::dll<Anon_45,n,S>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 48::ref [x]
                              x'::dll<Anon_46,flted_207_216,S1>@M[Orig][LHSCase] * 
                              res::dll<Anon_47,flted_207_215,S2>@M[Orig][LHSCase]&
                              flted_207_216=1 & flted_207_215+1=n & union(S1,
                              S2)=S & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4947:exists(v_4946:exists(S1_4889:exists(v_4887:exists(v_4902:exists(S1_4904:(S1_4889= | 
  S1_4889=union(S1_4947,{v_4946})) & S1=union(S1_4904,{v_4902}) & 
  S=union(S1_4889,{v_4887}) & S1_4889=S2 & v_4887=v_4902 & S1_4904= & 
  S1_4904=))))))) --> GN(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[Anon_63; n; 
                    S](ex)x::dll<Anon_63,n,S>@M[Orig][LHSCase]&1<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 62::
                                EXISTS(flted_253_207,Anon_64,
                                S2: res::dll<Anon_64,flted_253_207,S2>@M[Orig][LHSCase]&
                                flted_253_207+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_63; n; 
                  S](ex)x::dll<Anon_63,n,S>@M[Orig][LHSCase]&2<=n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 62::
                              res::dll<Anon_64,flted_253_207,S2>@M[Orig][LHSCase]&
                              flted_253_207+2=n & S2<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5061:exists(v_5060:exists(v_4986:exists(S1_4988:exists(S1_5030:exists(v_5028:(S1_5030= | 
  S1_5030=union(S1_5061,{v_5060})) & S=union(S1_4988,{v_4986}) & 
  S1_5030=S2 & S1_4988=union(S1_5030,{v_5028})))))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INSERT(S,S1,a)
!!! POST:  S1=union(S,{a})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSERT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 63::
                                EXISTS(p_205,m,
                                S1: x::dll<p_205,m,S1>@M[Orig][LHSCase]&m=1+
                                n & INSERT(S,S1,a) & p_205=p&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 63::
                              x::dll<p_205,m,S1>@M[Orig][LHSCase]&m=1+n & 
                              p_205=p & S1=union(S,{a}) & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5193:exists(v_5191:exists(S1_5105:exists(v_5103:exists(S1_5176:exists(v_5174:S1_5193= & 
  S1_5176=union(S1_5193,{v_5191}) & S1_5176=union(S1_5193,{v_5191}) & 
  S1_5105= & v_5103=v_5174 & a=v_5191 & S=union(S1_5105,{v_5103}) & 
  S1=union(S1_5176,{v_5174})))))))) --> INSERT(S,S1,a),
 (exists(S1_5294:exists(v_5293:exists(S1_5105:exists(v_5103:exists(S1_5245:exists(v_5243:S1_5242=union(S1_5294,
  {v_5293}) & S1_5242=S1_5245 & v_5103=v_5243 & S1_5105=S_5145 & 
  INSERT(S_5145,S1_5242,a) & S=union(S1_5105,{v_5103}) & S1=union(S1_5245,
  {v_5243})))))))) --> INSERT(S,S1,a)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...

!!! REL :  CPY(S,S2)
!!! POST:  S2=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 108::
                                EXISTS(p_176,n_177,S_178,n_179,Anon_73,
                                S2: x::dll<p_176,n_177,S_178>@M[Orig][LHSCase] * 
                                res::dll<Anon_73,n_179,S2>@M[Orig][LHSCase]&
                                CPY(S,S2) & p_176=p & n_177=n & S_178=S & 
                                n_179=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 108::
                              x::dll<p_176,n_177,S_178>@M[Orig][LHSCase] * 
                              res::dll<Anon_73,n_179,S2>@M[Orig][LHSCase]&
                              p_176=p & n_177=n & S_178=S & n_179=n & S2=S & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_5347:exists(v_5706:exists(v_5345:exists(S1_5708:exists(S_178:exists(S1_5657:exists(v_5655:S2=union(S1_5708,
  {v_5706}) & S=union(S1_5347,{v_5345}) & CPY(S_5353,S2_5395) & 
  S_5353=S1_5347 & S1_5657=S1_5347 & v_5706=v_5655 & v_5345=v_5655 & 
  S1_5708=S2_5395 & S_5353= & S1_5657= & S1_5657= & S2_5395= & S1_5708= & 
  S1_5708= & S_178=union(S1_5657,{v_5655}))))))))) --> CPY(S,S2),
 (exists(S1_5347:exists(v_5706:exists(v_5345:exists(S1_5708:exists(S_178:exists(S1_5657:exists(v_5655:S2=union(S1_5708,
  {v_5706}) & S=union(S1_5347,{v_5345}) & CPY(S_5353,S2_5395) & 
  S_5353=S1_5347 & S1_5657=S1_5347 & v_5706=v_5655 & v_5345=v_5655 & 
  S1_5708=S2_5395 & S2_5395= & S_5353= & S1_5657= & S1_5657= & S1_5708= & 
  S1_5708= & S_178=union(S1_5657,{v_5655}))))))))) --> CPY(S,S2),
 (exists(S1_5347:exists(v_5739:exists(v_5345:exists(S1_5741:exists(S_178:exists(S1_5657:exists(v_5655:S2=union(S1_5741,
  {v_5739}) & S=union(S1_5347,{v_5345}) & CPY(S_5353,S2_5395) & 
  S_5353=S1_5347 & S1_5657=S1_5347 & v_5739=v_5655 & v_5345=v_5655 & 
  S1_5741=S2_5395 & S_5353= & S1_5657= & S1_5657= & S2_5395= & S1_5741= & 
  S1_5741= & S_178=union(S1_5657,{v_5655}))))))))) --> CPY(S,S2),
 (exists(S_178:S2= & S= & S_178=S & S_178= & S_178=)) --> CPY(S,S2),
 (exists(S1_5637:exists(v_5636:exists(S1_5347:exists(v_5545:exists(v_5345:exists(S1_5634:exists(v_5633:exists(S1_5547:exists(S_178:exists(S1_5487:exists(v_5485:exists(S1_5480:exists(S1_5567:exists(v_5478:exists(v_5565:(S1_5480= | 
  S1_5480=union(S1_5637,{v_5636})) & S2=union(S1_5547,{v_5545}) & 
  S=union(S1_5347,{v_5345}) & CPY(S_5353,S2_5395) & S1_5487=S1_5347 & 
  S_5353=S1_5347 & v_5545=v_5485 & v_5345=v_5485 & S_5353=union(S1_5634,
  {v_5633}) & S2_5395=union(S1_5480,{v_5478}) & S1_5547=union(S1_5567,
  {v_5565}) & S1_5547=union(S1_5567,{v_5565}) & S_178=union(S1_5487,
  {v_5485}) & S1_5480=S1_5567 & v_5478=v_5565)))))))))))))))) --> CPY(S,S2),
 (exists(S_178:exists(v_5655:exists(S1_5657:exists(S1_5347:exists(v_5345:exists(S1_5741:exists(v_5739:S_178=union(S1_5657,
  {v_5655}) & S1_5741= & S1_5741= & S1_5657= & S1_5657= & S2_5395= & 
  S_5353= & S1_5741=S2_5395 & v_5345=v_5655 & v_5739=v_5655 & 
  S1_5657=S1_5347 & S_5353=S1_5347 & CPY(S_5353,S2_5395) & S=union(S1_5347,
  {v_5345}) & S2=union(S1_5741,{v_5739}))))))))) --> CPY(S,S2),
 (exists(S_178:S_178= & S_178=S & S= & S2=)) --> CPY(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...
Timeout when checking #simplify  Restarting Omega after ... 275 invocations Stop Omega... 275 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 276 invocations Stop Omega... 276 invocations Starting Omega...oc

!!! REL :  FIL(S,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[Anon_74; n; 
                    S](ex)x::dll<Anon_74,n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 130::ref [x]
                                EXISTS(Anon_75,m,
                                S2: res::dll<Anon_75,m,S2>@M[Orig][LHSCase]&
                                m<=n & FIL(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_74; n; 
                  S](ex)x::dll<Anon_74,n,S>@M[Orig][LHSCase]&0<=n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 130::ref [x]
                              res::dll<Anon_75,m,S2>@M[Orig][LHSCase]&m<=n & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(Anon_6051:exists(self_5943:exists(flted_12_5944:exists(n_6052:exists(x':exists(res:exists(v_node_503_872':exists(tmp_171':exists(self_6348:exists(Anon_6103:exists(m_6104:exists(flted_12_6349:exists(p_5942:exists(Anon_75:exists(Anon_74:exists(m:exists(v_bool_490_870':exists(v_bool_498_866':exists(q_6335:exists(v:exists(x:exists(n:exists(v_bool_489_871':exists(v_6334:exists(S1_5947:exists(v_5945:exists(S1_6336:(Anon_6051=x & 
  self_5943=x & S1_5947=S_6053 & 1+flted_12_5944=n & 1+n_6052=n & x'=x & 
  res=x & v_node_503_872'=x & v_5945=v_6334 & tmp_171'=q_6335 & 
  self_6348=Anon_6103 & flted_12_6349=0 & S1_6336=S2_6105 & m_6104=0 & 
  p_5942=Anon_74 & Anon_75=Anon_74 & m=1 & (1+v)<=v_6334 & 
  !(v_bool_490_870') & !(v_bool_498_866') & q_6335=null & x!=null & 1<=n & 
  FIL(S_6053,S2_6105) & v_bool_489_871' | Anon_6051=x & self_5943=x & 
  S1_5947=S_6053 & 1+flted_12_5944=n & 1+n_6052=n & x'=x & res=x & 
  v_node_503_872'=x & v_5945=v_6334 & tmp_171'=q_6335 & 
  self_6348=Anon_6103 & flted_12_6349=0 & S1_6336=S2_6105 & m_6104=0 & 
  p_5942=Anon_74 & Anon_75=Anon_74 & m=1 & !(v_bool_490_870') & 
  !(v_bool_498_866') & q_6335=null & (1+v_6334)<=v & x!=null & 1<=n & 
  FIL(S_6053,S2_6105) & v_bool_489_871' | Anon_6051=x & self_5943=x & 
  S1_5947=S_6053 & 1+flted_12_5944=n & 1+n_6052=n & x'=x & res=x & 
  v_node_503_872'=x & v_5945=v_6334 & self_6348=Anon_6103 & m_6104=0 & 
  flted_12_6349=0 & S1_6336=S2_6105 & tmp_171'=q_6335 & p_5942=Anon_74 & 
  Anon_75=Anon_74 & m=1 & (1+v)<=v_6334 & !(v_bool_490_870') & 
  !(v_bool_498_866') & q_6335=null & x!=null & 1<=n & FIL(S_6053,S2_6105) & 
  v_bool_489_871' | Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+
  flted_12_5944=n & 1+n_6052=n & x'=x & res=x & v_node_503_872'=x & 
  v_5945=v_6334 & self_6348=Anon_6103 & m_6104=0 & flted_12_6349=0 & 
  S1_6336=S2_6105 & tmp_171'=q_6335 & p_5942=Anon_74 & Anon_75=Anon_74 & 
  m=1 & !(v_bool_490_870') & !(v_bool_498_866') & q_6335=null & (1+
  v_6334)<=v & x!=null & 1<=n & FIL(S_6053,S2_6105) & v_bool_489_871' | 
  (Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+flted_12_5944=n & 1+
  n_6052=n & x'=x & res=x & v_node_503_872'=x & v_5945=v_6334 & 
  tmp_171'=q_6335 & self_6348=Anon_6103 & m_6104=0 & flted_12_6349=0 & 
  S1_6336=S2_6105 & p_5942=Anon_74 & Anon_75=Anon_74 & m=1 & (1+v)<=v_6334 & 
  !(v_bool_490_870') & !(v_bool_498_866') & q_6335=null & x!=null & 1<=n & 
  FIL(S_6053,S2_6105) & v_bool_489_871' | Anon_6051=x & self_5943=x & 
  S1_5947=S_6053 & 1+flted_12_5944=n & 1+n_6052=n & x'=x & res=x & 
  v_node_503_872'=x & v_5945=v_6334 & tmp_171'=q_6335 & 
  self_6348=Anon_6103 & m_6104=0 & flted_12_6349=0 & S1_6336=S2_6105 & 
  p_5942=Anon_74 & Anon_75=Anon_74 & m=1 & !(v_bool_490_870') & 
  !(v_bool_498_866') & q_6335=null & (1+v_6334)<=v & x!=null & 1<=n & 
  FIL(S_6053,S2_6105) & v_bool_489_871') & S2_6105=) & S2=union(S1_6336,
  {v_6334}) & S=union(S1_5947,{v_5945}) & S2_6105= & S1_6336= & 
  S1_6336=)))))))))))))))))))))))))))) --> FIL(S,S2),
 (S2= & S= & S2=S) --> FIL(S,S2),
 (exists(S1_6229:exists(v_6228:exists(v_5945:exists(S1_5947:exists(Anon_11:exists(v:(S2_6201= | 
  S2_6201=union(S1_6229,{v_6228})) & S=union(S1_5947,{v_5945}) & 
  FIL(S_6004,S2_6201) & S2_6201=S2 & v_5945=v & S1_5947=S_6004 & 
  Anon_11=v))))))) --> FIL(S,S2),
 (exists(Anon_6117:exists(p_6178:exists(Anon_6051:exists(self_5943:exists(flted_12_5944:exists(m_6118:exists(n_6052:exists(x':exists(res:exists(v_node_503_872':exists(q_6239:exists(tmp_171':exists(q_6182:exists(p_5942:exists(Anon_75:exists(Anon_74:exists(flted_12_6180:exists(m:exists(flted_12_156_6312:exists(n:exists(v_bool_490_870':exists(v:exists(q_6256:exists(self_6179:exists(x:exists(v_bool_498_866':exists(v_bool_489_871':exists(S1_6314:exists(v_6313:exists(v_6238:exists(S1_5947:exists(v_5945:exists(S1_6183:exists(v_6181:exists(S1_6240:exists(S1_6257:exists(v_6255:(S1_6183= & 
  (Anon_6117=p_6178 & Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+
  flted_12_5944=n & m_6118=1 & 1+n_6052=n & x'=x & res=x & 
  v_node_503_872'=x & v_5945=v_6238 & q_6239=self_6179 & 
  tmp_171'=self_6179 & v_6181=v_6255 & q_6182=q_6256 & S1_6183=S1_6257 & 
  p_5942=Anon_74 & Anon_75=Anon_74 & flted_12_6180=0 & m=2 & (1+v)<=v_6238 & 
  !(v_bool_490_870') & q_6256=null & self_6179!=null & x!=null & 2<=n & 
  v_bool_498_866' & v_bool_489_871' & FIL(S_6053,S2_6119) | 
  Anon_6117=p_6178 & Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+
  flted_12_5944=n & m_6118=1 & 1+n_6052=n & x'=x & res=x & 
  v_node_503_872'=x & v_5945=v_6238 & q_6239=self_6179 & 
  tmp_171'=self_6179 & v_6181=v_6255 & q_6182=q_6256 & S1_6183=S1_6257 & 
  p_5942=Anon_74 & Anon_75=Anon_74 & flted_12_6180=0 & m=2 & 
  !(v_bool_490_870') & (1+v_6238)<=v & q_6256=null & self_6179!=null & 
  x!=null & 2<=n & v_bool_498_866' & v_bool_489_871' & 
  FIL(S_6053,S2_6119)) | (Anon_6117=p_6178 & Anon_6051=x & self_5943=x & 
  S1_5947=S_6053 & 1+flted_12_5944=n & -2+m_6118=flted_12_156_6312 & 1+
  n_6052=n & x'=x & res=x & v_node_503_872'=x & v_5945=v_6238 & 
  q_6239=self_6179 & tmp_171'=self_6179 & v_6181=v_6255 & q_6182=q_6256 & 
  S1_6183=S1_6257 & p_5942=Anon_74 & Anon_75=Anon_74 & -1+
  flted_12_6180=flted_12_156_6312 & -3+m=flted_12_156_6312 & 
  0<=flted_12_156_6312 & (3+flted_12_156_6312)<=n & (1+v)<=v_6238 & 
  !(v_bool_490_870') & q_6256!=null & self_6179!=null & x!=null & 
  v_bool_498_866' & v_bool_489_871' & FIL(S_6053,S2_6119) | 
  Anon_6117=p_6178 & Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+
  flted_12_5944=n & -2+m_6118=flted_12_156_6312 & 1+n_6052=n & x'=x & 
  res=x & v_node_503_872'=x & v_5945=v_6238 & q_6239=self_6179 & 
  tmp_171'=self_6179 & v_6181=v_6255 & q_6182=q_6256 & S1_6183=S1_6257 & 
  p_5942=Anon_74 & Anon_75=Anon_74 & -1+flted_12_6180=flted_12_156_6312 & -3+
  m=flted_12_156_6312 & 0<=flted_12_156_6312 & (3+flted_12_156_6312)<=n & 
  !(v_bool_490_870') & (1+v_6238)<=v & q_6256!=null & self_6179!=null & 
  x!=null & v_bool_498_866' & v_bool_489_871' & FIL(S_6053,S2_6119)) & 
  S1_6183=union(S1_6314,{v_6313})) & S2=union(S1_6240,{v_6238}) & 
  S=union(S1_5947,{v_5945}) & S2_6119=union(S1_6183,{v_6181}) & 
  S1_6240=union(S1_6257,{v_6255}) & S1_6240=union(S1_6257,
  {v_6255}))))))))))))))))))))))))))))))))))))))) --> FIL(S,S2),
 (exists(Anon_6051:exists(self_5943:exists(flted_12_5944:exists(n_6052:exists(x':exists(res:exists(v_node_503_872':exists(tmp_171':exists(self_6348:exists(Anon_6103:exists(m_6104:exists(flted_12_6349:exists(p_5942:exists(Anon_75:exists(Anon_74:exists(m:exists(v_bool_490_870':exists(v_bool_498_866':exists(q_6335:exists(v:exists(x:exists(n:exists(v_bool_489_871':exists(S1_5947:exists(v_5945:exists(S1_6336:exists(v_6334:S1_6336= & 
  S1_6336= & S2_6105= & (Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+
  flted_12_5944=n & 1+n_6052=n & x'=x & res=x & v_node_503_872'=x & 
  v_5945=v_6334 & tmp_171'=q_6335 & self_6348=Anon_6103 & m_6104=0 & 
  flted_12_6349=0 & S1_6336=S2_6105 & p_5942=Anon_74 & Anon_75=Anon_74 & 
  m=1 & (1+v)<=v_6334 & !(v_bool_490_870') & !(v_bool_498_866') & 
  q_6335=null & x!=null & 1<=n & FIL(S_6053,S2_6105) & v_bool_489_871' | 
  Anon_6051=x & self_5943=x & S1_5947=S_6053 & 1+flted_12_5944=n & 1+
  n_6052=n & x'=x & res=x & v_node_503_872'=x & v_5945=v_6334 & 
  tmp_171'=q_6335 & self_6348=Anon_6103 & m_6104=0 & flted_12_6349=0 & 
  S1_6336=S2_6105 & p_5942=Anon_74 & Anon_75=Anon_74 & m=1 & 
  !(v_bool_490_870') & !(v_bool_498_866') & q_6335=null & (1+v_6334)<=v & 
  x!=null & 1<=n & FIL(S_6053,S2_6105) & v_bool_489_871') & S=union(S1_5947,
  {v_5945}) & S2=union(S1_6336,
  {v_6334}))))))))))))))))))))))))))))) --> FIL(S,S2),
 (S2=S & S= & S2=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of mona aborted execution
Restarting Mona ...
Timeout when checking #simplify  Restarting Omega after ... 330 invocations Stop Omega... 330 invocations Starting Omega...oc
Timeout when checking #simplify  Restarting Omega after ... 331 invocations Stop Omega... 331 invocations Starting Omega...oc

!!! REL :  RMV2(S,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RMV2]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 119::
                                EXISTS(p_172,m,
                                S2: res::dll<p_172,m,S2>@M[Orig][LHSCase]&
                                m<=n & RMV2(S,S2) & p_172=p&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&0<=n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 119::
                              res::dll<p_172,m,S2>@M[Orig][LHSCase]&m<=n & 
                              p_172=p & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_7184:exists(S1_7186:exists(Anon_11:exists(v:S2= & S=union(S1_7186,
  {v_7184}) & S2=S1_7186 & v_7184=v & S1_7186= & 
  Anon_11=v))))) --> RMV2(S,S2),
 (exists(flted_12_7183:exists(n_7346:exists(self_7182:exists(res:exists(v_node_477_922':exists(tmp_173':exists(p_7345:exists(self_7677:exists(m_7395:exists(flted_12_7678:exists(m:exists(p_7181:exists(p_172:exists(p:exists(v_bool_463_920':exists(v:exists(q_7664:exists(v_bool_472_916':exists(x:exists(n:exists(v_bool_462_921':exists(v_7663:exists(S1_7186:exists(v_7184:exists(S1_7665:(S1_7186=S_7347 & 
  1+flted_12_7183=n & 1+n_7346=n & self_7182=x & res=x & v_node_477_922'=x & 
  v_7184=v_7663 & tmp_173'=q_7664 & p_7345=x & self_7677=x & 
  flted_12_7678=0 & S1_7665=S2_7396 & m_7395=0 & m=1 & p_7181=p & p_172=p & 
  (1+v)<=v_7663 & !(v_bool_463_920') & q_7664=null & !(v_bool_472_916') & 
  x!=null & 1<=n & RMV2(S_7347,S2_7396) & v_bool_462_921' | S1_7186=S_7347 & 
  1+flted_12_7183=n & 1+n_7346=n & self_7182=x & res=x & v_node_477_922'=x & 
  v_7184=v_7663 & tmp_173'=q_7664 & p_7345=x & self_7677=x & 
  flted_12_7678=0 & S1_7665=S2_7396 & m_7395=0 & m=1 & p_7181=p & p_172=p & 
  !(v_bool_463_920') & (1+v_7663)<=v & q_7664=null & !(v_bool_472_916') & 
  x!=null & 1<=n & RMV2(S_7347,S2_7396) & v_bool_462_921' | S1_7186=S_7347 & 
  1+flted_12_7183=n & 1+n_7346=n & self_7182=x & res=x & v_node_477_922'=x & 
  v_7184=v_7663 & p_7345=x & self_7677=x & m_7395=0 & flted_12_7678=0 & 
  S1_7665=S2_7396 & tmp_173'=q_7664 & m=1 & p_7181=p & p_172=p & (1+
  v)<=v_7663 & !(v_bool_463_920') & q_7664=null & !(v_bool_472_916') & 
  x!=null & 1<=n & RMV2(S_7347,S2_7396) & v_bool_462_921' | S1_7186=S_7347 & 
  1+flted_12_7183=n & 1+n_7346=n & self_7182=x & res=x & v_node_477_922'=x & 
  v_7184=v_7663 & p_7345=x & self_7677=x & m_7395=0 & flted_12_7678=0 & 
  S1_7665=S2_7396 & tmp_173'=q_7664 & m=1 & p_7181=p & p_172=p & 
  !(v_bool_463_920') & (1+v_7663)<=v & q_7664=null & !(v_bool_472_916') & 
  x!=null & 1<=n & RMV2(S_7347,S2_7396) & v_bool_462_921' | 
  (S1_7186=S_7347 & 1+flted_12_7183=n & 1+n_7346=n & self_7182=x & res=x & 
  v_node_477_922'=x & v_7184=v_7663 & tmp_173'=q_7664 & p_7345=x & 
  self_7677=x & m_7395=0 & flted_12_7678=0 & S1_7665=S2_7396 & m=1 & 
  p_7181=p & p_172=p & (1+v)<=v_7663 & !(v_bool_463_920') & q_7664=null & 
  !(v_bool_472_916') & x!=null & 1<=n & RMV2(S_7347,S2_7396) & 
  v_bool_462_921' | S1_7186=S_7347 & 1+flted_12_7183=n & 1+n_7346=n & 
  self_7182=x & res=x & v_node_477_922'=x & v_7184=v_7663 & 
  tmp_173'=q_7664 & p_7345=x & self_7677=x & m_7395=0 & flted_12_7678=0 & 
  S1_7665=S2_7396 & m=1 & p_7181=p & p_172=p & !(v_bool_463_920') & (1+
  v_7663)<=v & q_7664=null & !(v_bool_472_916') & x!=null & 1<=n & 
  RMV2(S_7347,S2_7396) & v_bool_462_921') & S2_7396=) & S2=union(S1_7665,
  {v_7663}) & S=union(S1_7186,{v_7184}) & S2_7396= & S1_7665= & 
  S1_7665=)))))))))))))))))))))))))) --> RMV2(S,S2),
 (S2= & S= & S2=S) --> RMV2(S,S2),
 (exists(S1_7543:exists(v_7542:exists(v_7184:exists(v_7483:exists(S1_7485:exists(S1_7186:exists(S1_7318:exists(v_7316:exists(Anon_11:exists(v:(S1_7318= | 
  S1_7318=union(S1_7543,{v_7542})) & S2=union(S1_7485,{v_7483}) & 
  S=union(S1_7186,{v_7184}) & v_7184=v & v_7316=v_7483 & S1_7318=S1_7485 & 
  S1_7186=union(S1_7318,{v_7316}) & Anon_11=v))))))))))) --> RMV2(S,S2),
 (exists(Anon_11:exists(v:exists(S1_7186:exists(v_7184:Anon_11=v & 
  S1_7186= & v_7184=v & S2=S1_7186 & S=union(S1_7186,{v_7184}) & 
  S2=))))) --> RMV2(S,S2),
 (exists(x:exists(p_7345:exists(flted_12_7183:exists(m_7407:exists(n_7346:exists(self_7182:exists(res:exists(v_node_477_922':exists(q_7568:exists(tmp_173':exists(q_7471:exists(flted_12_7469:exists(m:exists(p_7181:exists(p_172:exists(p:exists(flted_12_156_7641:exists(n:exists(v:exists(v_bool_463_920':exists(q_7585:exists(self_7468:exists(p_7467:exists(v_bool_472_916':exists(v_bool_462_921':exists(S1_7643:exists(v_7642:exists(v_7567:exists(S1_7186:exists(v_7184:exists(S1_7472:exists(v_7470:exists(S1_7569:exists(S1_7586:exists(v_7584:(S1_7472= & 
  (x=p_7467 & p_7345=p_7467 & S1_7186=S_7347 & 1+flted_12_7183=n & 
  m_7407=1 & 1+n_7346=n & self_7182=p_7467 & res=p_7467 & 
  v_node_477_922'=p_7467 & v_7184=v_7567 & q_7568=self_7468 & 
  tmp_173'=self_7468 & v_7470=v_7584 & q_7471=q_7585 & S1_7472=S1_7586 & 
  flted_12_7469=0 & m=2 & p_7181=p & p_172=p & (1+v)<=v_7567 & 
  !(v_bool_463_920') & q_7585=null & self_7468!=null & p_7467!=null & 2<=n & 
  v_bool_472_916' & v_bool_462_921' & RMV2(S_7347,S2_7408) | x=p_7467 & 
  p_7345=p_7467 & S1_7186=S_7347 & 1+flted_12_7183=n & m_7407=1 & 1+
  n_7346=n & self_7182=p_7467 & res=p_7467 & v_node_477_922'=p_7467 & 
  v_7184=v_7567 & q_7568=self_7468 & tmp_173'=self_7468 & v_7470=v_7584 & 
  q_7471=q_7585 & S1_7472=S1_7586 & flted_12_7469=0 & m=2 & p_7181=p & 
  p_172=p & (1+v_7567)<=v & !(v_bool_463_920') & q_7585=null & 
  self_7468!=null & p_7467!=null & 2<=n & v_bool_472_916' & 
  v_bool_462_921' & RMV2(S_7347,S2_7408)) | (x=p_7467 & p_7345=p_7467 & 
  S1_7186=S_7347 & 1+flted_12_7183=n & -2+m_7407=flted_12_156_7641 & 1+
  n_7346=n & self_7182=p_7467 & res=p_7467 & v_node_477_922'=p_7467 & 
  v_7184=v_7567 & q_7568=self_7468 & tmp_173'=self_7468 & v_7470=v_7584 & 
  q_7471=q_7585 & S1_7472=S1_7586 & -1+flted_12_7469=flted_12_156_7641 & -3+
  m=flted_12_156_7641 & p_7181=p & p_172=p & 0<=flted_12_156_7641 & (3+
  flted_12_156_7641)<=n & (1+v)<=v_7567 & !(v_bool_463_920') & 
  q_7585!=null & self_7468!=null & p_7467!=null & v_bool_472_916' & 
  v_bool_462_921' & RMV2(S_7347,S2_7408) | x=p_7467 & p_7345=p_7467 & 
  S1_7186=S_7347 & 1+flted_12_7183=n & -2+m_7407=flted_12_156_7641 & 1+
  n_7346=n & self_7182=p_7467 & res=p_7467 & v_node_477_922'=p_7467 & 
  v_7184=v_7567 & q_7568=self_7468 & tmp_173'=self_7468 & v_7470=v_7584 & 
  q_7471=q_7585 & S1_7472=S1_7586 & -1+flted_12_7469=flted_12_156_7641 & -3+
  m=flted_12_156_7641 & p_7181=p & p_172=p & 0<=flted_12_156_7641 & (3+
  flted_12_156_7641)<=n & (1+v_7567)<=v & !(v_bool_463_920') & 
  q_7585!=null & self_7468!=null & p_7467!=null & v_bool_472_916' & 
  v_bool_462_921' & RMV2(S_7347,S2_7408)) & S1_7472=union(S1_7643,
  {v_7642})) & S2=union(S1_7569,{v_7567}) & S=union(S1_7186,{v_7184}) & 
  S2_7408=union(S1_7472,{v_7470}) & S1_7569=union(S1_7586,{v_7584}) & 
  S1_7569=union(S1_7586,
  {v_7584}))))))))))))))))))))))))))))))))))))) --> RMV2(S,S2),
 (exists(flted_12_7183:exists(n_7346:exists(self_7182:exists(res:exists(v_node_477_922':exists(tmp_173':exists(p_7345:exists(self_7677:exists(m_7395:exists(flted_12_7678:exists(m:exists(p_7181:exists(p_172:exists(p:exists(v_bool_463_920':exists(v:exists(q_7664:exists(v_bool_472_916':exists(x:exists(n:exists(v_bool_462_921':exists(S1_7186:exists(v_7184:exists(S1_7665:exists(v_7663:S1_7665= & 
  S1_7665= & S2_7396= & (S1_7186=S_7347 & 1+flted_12_7183=n & 1+n_7346=n & 
  self_7182=x & res=x & v_node_477_922'=x & v_7184=v_7663 & 
  tmp_173'=q_7664 & p_7345=x & self_7677=x & m_7395=0 & flted_12_7678=0 & 
  S1_7665=S2_7396 & m=1 & p_7181=p & p_172=p & (1+v)<=v_7663 & 
  !(v_bool_463_920') & q_7664=null & !(v_bool_472_916') & x!=null & 1<=n & 
  RMV2(S_7347,S2_7396) & v_bool_462_921' | S1_7186=S_7347 & 1+
  flted_12_7183=n & 1+n_7346=n & self_7182=x & res=x & v_node_477_922'=x & 
  v_7184=v_7663 & tmp_173'=q_7664 & p_7345=x & self_7677=x & m_7395=0 & 
  flted_12_7678=0 & S1_7665=S2_7396 & m=1 & p_7181=p & p_172=p & 
  !(v_bool_463_920') & (1+v_7663)<=v & q_7664=null & !(v_bool_472_916') & 
  x!=null & 1<=n & RMV2(S_7347,S2_7396) & v_bool_462_921') & S=union(S1_7186,
  {v_7184}) & S2=union(S1_7665,
  {v_7663}))))))))))))))))))))))))))) --> RMV2(S,S2),
 (S2=S & S= & S2=) --> RMV2(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[p; n; 
                    S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 105::
                                EXISTS(p_182,n_183,
                                S2: x::dll<p_182,n_183,S2>@M[Orig][LHSCase]&
                                TRAV(S1,S2) & p_182=p & n_183=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S1](ex)x::dll<p,n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 105::
                              x::dll<p_182,n_183,S2>@M[Orig][LHSCase]&
                              p_182=p & n_183=n & S1=S2 & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S1= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_7970:exists(v_7969:exists(S1_7886:exists(v_7884:exists(v_7922:exists(S1_7924:(S2_7921= | 
  S2_7921=union(S1_7970,{v_7969})) & S2=union(S1_7924,{v_7922}) & 
  S1=union(S1_7886,{v_7884}) & TRAV(S1_7892,S2_7921) & S1_7886=S1_7892 & 
  v_7884=v_7922 & S2_7921=S1_7924))))))) --> TRAV(S1,S2),
 (S2=S1 & S1= & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  PF(S1,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_39; m; 
                    S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(flted_112_224,Anon_40,
                                S2: x'::dll<Anon_40,flted_112_224,S2>@M[Orig][LHSCase]&
                                flted_112_224+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39; m; 
                  S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              x'::dll<Anon_40,flted_112_224,S2>@M[Orig][LHSCase]&
                              flted_112_224+1=m & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_8040:exists(S1_8042:S2= & S1=union(S1_8042,{v_8040}) & 
  S2=S1_8042 & S1_8042=))) --> PF(S1,S2),
 (exists(S1_8042:exists(v_8040:S1_8042= & S2=S1_8042 & S1=union(S1_8042,
  {v_8040}) & S2=))) --> PF(S1,S2),
 (exists(S1_8201:exists(v_8200:exists(v_8040:exists(v_8145:exists(S1_8147:exists(S1_8042:exists(S1_8118:exists(v_8116:(S1_8118= | 
  S1_8118=union(S1_8201,{v_8200})) & S2=union(S1_8147,{v_8145}) & 
  S1=union(S1_8042,{v_8040}) & v_8116=v_8145 & S1_8118=S1_8147 & 
  S1_8042=union(S1_8118,{v_8116})))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
!!! REL :  PUF(S1,S,v)
!!! POST:  S=S1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PUF]
              EBase exists (Expl)(Impl)[Anon_36; n; 
                    S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(v_226,n_227,Anon_37,q,Anon_38,
                                S1: x'::node<v_226,Anon_37,q>@M[Orig] * 
                                q::dll<Anon_38,n_227,S1>@M[Orig][LHSCase]&
                                PUF(S1,S,v) & v_226=v & n_227=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36; n; 
                  S](ex)x::dll<Anon_36,n,S>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::node<v_226,Anon_37,q>@M[Orig] * 
                              q::dll<Anon_38,n_227,S1>@M[Orig][LHSCase]&
                              v_226=v & n_227=n & S=S1 & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_226:S1= & S= & S1=S & v=v_226)) --> PUF(S1,S,v),
 (exists(v_226:v=v_226 & S1=S & S= & S1=)) --> PUF(S1,S,v),
 (exists(S1_8367:exists(v_8366:exists(v_226:exists(v_8284:exists(v_8320:exists(S1_8286:exists(S1_8322:(S1_8286= | 
  S1_8286=union(S1_8367,{v_8366})) & S1=union(S1_8322,{v_8320}) & 
  S=union(S1_8286,{v_8284}) & v=v_226 & v_8284=v_8320 & 
  S1_8286=S1_8322)))))))) --> PUF(S1,S,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_43; n; 
                    S1](ex)x::dll<Anon_43,n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(n_218,Anon_44,
                                S2: x::dll<Anon_44,n_218,S2>@M[Orig][LHSCase]&
                                n_218=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_43; n; 
                  S1](ex)x::dll<Anon_43,n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              x::dll<Anon_44,n_218,S2>@M[Orig][LHSCase]&
                              res=x & Anon_43=Anon_44 & S1=S2 & n=n_218 & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  REV(S,S1,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REV]
              EBase exists (Expl)(Impl)[Anon_68; n; S1; Anon_69; m; 
                    S2](ex)xs::dll<Anon_68,n,S1>@M[Orig][LHSCase] * 
                    ys::dll<Anon_69,m,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 90::ref [xs;ys]
                                EXISTS(flted_360_195,Anon_70,
                                S: ys'::dll<Anon_70,flted_360_195,S>@M[Orig][LHSCase]&
                                flted_360_195=m+n & xs'=null & REV(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_68; n; S1; Anon_69; m; 
                  S2](ex)xs::dll<Anon_68,n,S1>@M[Orig][LHSCase] * 
                  ys::dll<Anon_69,m,S2>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 90::ref [xs;ys]
                              ys'::dll<Anon_70,flted_360_195,S>@M[Orig][LHSCase]&
                              flted_360_195=m+n & xs'=null & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_8582:exists(S1_8811:exists(v_8810:exists(S1_8602:exists(v_8600:exists(v_8580:exists(S1_8556:exists(v_8554:exists(S1_8474:exists(v_8472:S2_8567=union(S1_8582,
  {v_8580}) & S1_8582=union(S1_8602,{v_8600}) & S1_8582=union(S1_8602,
  {v_8600}) & S_8777=union(S1_8811,{v_8810}) & S1_8556=S1_8602 & 
  v_8554=v_8600 & v_8472=v_8580 & S1_8474=S1_8564 & S_8777=S & 
  REV(S_8777,S1_8564,S2_8567) & S2=union(S1_8556,{v_8554}) & 
  S1=union(S1_8474,{v_8472})))))))))))) --> REV(S,S1,S2),
 (exists(S1_8474:exists(v_8472:exists(S1_8856:exists(v_8855:exists(S1_8697:exists(v_8695:S1=union(S1_8474,
  {v_8472}) & S2= & REV(S_8830,S1_8564,S2_8567) & S_8830=S & S1_8697=S2 & 
  S1_8474=S1_8564 & v_8472=v_8695 & S_8830=union(S1_8856,{v_8855}) & 
  S1_8697= & S1_8697= & S2_8567=union(S1_8697,
  {v_8695})))))))) --> REV(S,S1,S2),
 (exists(S1_8895:exists(v_8894:(S2= | S2=union(S1_8895,{v_8894})) & S1= & 
  S2=S))) --> REV(S,S1,S2),
 (exists(S1_8582:exists(S1_8945:exists(v_8944:exists(S1_8602:exists(v_8600:exists(v_8580:exists(S1_8556:exists(v_8554:exists(S1_8474:exists(v_8472:S2_8567=union(S1_8582,
  {v_8580}) & S1_8582=union(S1_8602,{v_8600}) & S1_8582=union(S1_8602,
  {v_8600}) & S_8916=union(S1_8945,{v_8944}) & S1_8556=S1_8602 & 
  v_8554=v_8600 & v_8472=v_8580 & S1_8474=S1_8564 & S_8916=S & 
  REV(S_8916,S1_8564,S2_8567) & S2=union(S1_8556,{v_8554}) & 
  S1=union(S1_8474,{v_8472})))))))))))) --> REV(S,S1,S2),
 (exists(S1_9000:exists(v_8999:exists(v_8695:exists(S1_8697:exists(S1_8474:exists(v_8472:S2_8567=union(S1_8697,
  {v_8695}) & S1_8697= & S1_8697= & S_8964=union(S1_9000,{v_8999}) & 
  v_8472=v_8695 & S1_8474=S1_8564 & S1_8697=S2 & S_8964=S & 
  REV(S_8964,S1_8564,S2_8567) & S2= & S1=union(S1_8474,
  {v_8472})))))))) --> REV(S,S1,S2),
 (exists(S1_9046:exists(v_9045:(S2= | S2=union(S1_9046,{v_9045})) & S1= & 
  S2=S))) --> REV(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! REL :  SN(S,S2,v)
!!! POST:  S2=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; Anon_48; t; Anon_49; Anon_50; 
                    Anon_51; j; 
                    S](ex)EXISTS(x_212: x::node<v,Anon_48,t>@M[Orig] * 
                    t::dll<x_212,Anon_49,Anon_50>@M[Orig][LHSCase] * 
                    y::dll<Anon_51,j,S>@M[Orig][LHSCase]&x!=null & x_212=x&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::ref [x]
                                EXISTS(Anon_52,k,
                                S2: x::dll<Anon_52,k,S2>@M[Orig][LHSCase]&
                                1<=k & k=1+j & SN(S,S2,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; Anon_48; t; Anon_49; Anon_50; 
                  Anon_51; j; S](ex)x::node<v,Anon_48,t>@M[Orig] * 
                  t::dll<x_212,Anon_49,Anon_50>@M[Orig][LHSCase] * 
                  y::dll<Anon_51,j,S>@M[Orig][LHSCase]&x_212=x & x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 51::ref [x]
                              x::dll<Anon_52,k,S2>@M[Orig][LHSCase]&1<=k & 
                              k=1+j & S2=union(S,{v}) & 0<=Anon_49 & 0<=j&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_9160:exists(S1_9162:S2=union(S1_9162,{v_9160}) & S= & S1_9162=S & 
  v=v_9160 & S1_9162= & S1_9162=))) --> SN(S,S2,v),
 (exists(v_9160:exists(S1_9162:S2=union(S1_9162,{v_9160}) & S= & S1_9162=S & 
  v=v_9160 & S1_9162= & S1_9162=))) --> SN(S,S2,v),
 (exists(S1_9305:exists(v_9304:exists(v_9224:exists(v_9156:exists(S1_9158:exists(S1_9226:exists(S1_9246:exists(v_9244:(S1_9158= | 
  S1_9158=union(S1_9305,{v_9304}) | S1_9158= | S1_9158=union(S1_9305,
  {v_9304})) & S2=union(S1_9226,{v_9224}) & S=union(S1_9158,{v_9156}) & 
  v=v_9224 & v_9156=v_9244 & S1_9158=S1_9246 & S1_9226=union(S1_9246,
  {v_9244}) & S1_9226=union(S1_9246,{v_9244})))))))))) --> SN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]:Timeout exception

[mona.ml]: Mona is preparing to restart because of Timeout when checking #999!
Restarting Mona ...

!!! REL :  SPI(S,S1,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPI]
              EBase exists (Expl)(Impl)[Anon_79; n; S1; Anon_80; m; 
                    S2](ex)x::dll<Anon_79,n,S1>@M[Orig][LHSCase] * 
                    y::dll<Anon_80,m,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 143::ref [x]
                                EXISTS(flted_531_168,Anon_81,
                                S: x'::dll<Anon_81,flted_531_168,S>@M[Orig][LHSCase]&
                                flted_531_168=n+m & SPI(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_79; n; S1; Anon_80; m; 
                  S2](ex)x::dll<Anon_79,n,S1>@M[Orig][LHSCase] * 
                  y::dll<Anon_80,m,S2>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 143::ref [x]
                              x'::dll<Anon_81,flted_531_168,S>@M[Orig][LHSCase]&
                              flted_531_168=n+m & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_9667:exists(S1_9712:exists(v_9665:exists(v_10085:exists(v_9710:exists(S1_10087:exists(S1_10104:exists(v_10102:S=union(S1_10087,
  {v_10085}) & S1=union(S1_9667,{v_9665}) & S2=union(S1_9712,{v_9710}) & 
  SPI(S_9817,S1_9739,S2_9742) & S1_9667=S1_9739 & S1_9712=S2_9742 & 
  v_9665=v_10085 & v_9710=v_10102 & S1_10104=S_9817 & S_9817= & S1_10104= & 
  S1_10104= & S1_10087=union(S1_10104,{v_10102}) & S1_10087=union(S1_10104,
  {v_10102})))))))))) --> SPI(S,S1,S2),
 (exists(S1_9935:exists(v_9934:(S2= | S2=union(S1_9935,{v_9934})) & S1= & 
  S2=S))) --> SPI(S,S1,S2),
 (exists(S1_10060:exists(v_10059:exists(S1_9667:exists(S1_9712:exists(v_9665:exists(v_9951:exists(v_9710:exists(S1_9953:exists(v_9968:exists(S1_9970:exists(S1_9904:exists(S1_9987:exists(v_9902:exists(v_9985:(S1_9904= | 
  S1_9904=union(S1_10060,{v_10059})) & S=union(S1_9953,{v_9951}) & 
  S1=union(S1_9667,{v_9665}) & S2=union(S1_9712,{v_9710}) & 
  SPI(S_9817,S1_9739,S2_9742) & S1_9667=S1_9739 & S1_9712=S2_9742 & 
  v_9665=v_9951 & v_9710=v_9968 & S_9817=union(S1_9904,{v_9902}) & 
  S1_9953=union(S1_9970,{v_9968}) & S1_9953=union(S1_9970,{v_9968}) & 
  S1_9970=union(S1_9987,{v_9985}) & S1_9970=union(S1_9987,{v_9985}) & 
  S1_9904=S1_9987 & v_9902=v_9985))))))))))))))) --> SPI(S,S1,S2),
 (exists(S1_10104:exists(v_10102:exists(S1_9712:exists(v_9710:exists(S1_9667:exists(v_9665:exists(S1_10087:exists(v_10085:S1_10087=union(S1_10104,
  {v_10102}) & S1_10087=union(S1_10104,{v_10102}) & S1_10104= & S1_10104= & 
  S_9817= & S1_10104=S_9817 & v_9710=v_10102 & v_9665=v_10085 & 
  S1_9712=S2_9742 & S1_9667=S1_9739 & SPI(S_9817,S1_9739,S2_9742) & 
  S2=union(S1_9712,{v_9710}) & S1=union(S1_9667,{v_9665}) & S=union(S1_10087,
  {v_10085})))))))))) --> SPI(S,S1,S2),
 (exists(S1_10189_10192:exists(v_10191:S1=S & S2= & S1=union(S1_10189_10192,
  {v_10191})))) --> SPI(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[p; n; 
                    S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&0<a & a<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 98::ref [x]
                                EXISTS(p_185,Anon_71,n2,n1,S1,
                                S2: x'::dll<p_185,n1,S1>@M[Orig][LHSCase] * 
                                res::dll<Anon_71,n2,S2>@M[Orig][LHSCase]&
                                n=n2+n1 & 0<n1 & 0<n2 & n1=a & 
                                SPLIT(S,S1,S2) & p_185=p&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; n; 
                  S](ex)x::dll<p,n,S>@M[Orig][LHSCase]&1<=a & a<n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 98::ref [x]
                              x'::dll<p_185,n1,S1>@M[Orig][LHSCase] * 
                              res::dll<Anon_71,n2,S2>@M[Orig][LHSCase]&n=n2+
                              n1 & 0<n1 & 0<n2 & n1=a & p_185=p & union(S1,
                              S2)=S & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_10420:exists(v_10419:exists(S1_10270:exists(v_10268:exists(S1_10379:exists(v_10377:S1_10379= & 
  S1_10379= & S1_10270=union(S1_10420,{v_10419}) & v_10268=v_10377 & 
  S1_10270=S2 & S=union(S1_10270,{v_10268}) & S1=union(S1_10379,
  {v_10377})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_10542:exists(v_10541:exists(S1_10545:exists(v_10544:exists(S1_10320:exists(v_10318:exists(S1_10441:exists(v_10439:S1_10435=union(S1_10542,
  {v_10541}) & S2_10436=union(S1_10545,{v_10544}) & S1_10435=S1_10441 & 
  v_10318=v_10439 & S1_10320=S_10323 & S2_10436=S2 & 
  SPLIT(S_10323,S1_10435,S2_10436) & S=union(S1_10320,{v_10318}) & 
  S1=union(S1_10441,{v_10439})))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                    S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase] * 
                    y::dll<Anon_31,m,S2>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_231,n_232,Anon_32,S3,Anon_33,
                                S4: x'::dll<Anon_32,m_231,S3>@M[Orig][LHSCase] * 
                                y'::dll<Anon_33,n_232,S4>@M[Orig][LHSCase]&
                                m_231=m & n_232=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_30; n; S1; Anon_31; m; 
                  S2](ex)x::dll<Anon_30,n,S1>@M[Orig][LHSCase] * 
                  y::dll<Anon_31,m,S2>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::dll<Anon_32,m_231,S3>@M[Orig][LHSCase] * 
                              y'::dll<Anon_33,n_232,S4>@M[Orig][LHSCase]&
                              y=x' & y'=x & Anon_31=Anon_32 & S2=S3 & 
                              Anon_30=Anon_33 & S1=S4 & m=m_231 & n=n_232 & 
                              0<=n & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


21 false contexts at: ( (540,6)  (237,13)  (237,4)  (339,4)  (339,11)  (349,6)  (349,13)  (348,6)  (348,6)  (346,6)  (346,13)  (345,8)  (344,27)  (344,14)  (344,9)  (343,10)  (343,4)  (342,8)  (342,12)  (342,4)  (342,4) )

Total verification time: 117.02 second(s)
	Time spent in main process: 8.52 second(s)
	Time spent in child processes: 108.5 second(s)
