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
!!! NEW RELS:[ (exists(S1_2031:exists(v_2030:(S2= | S2=union(S1_2031,{v_2030})) & S1= & 
  S2=S))) --> APP(S,S1,S2),
 (exists(S1_2129:exists(v_2128:exists(S1_1841:exists(v_1839:exists(v_2047:exists(S1_2049:exists(S1_1996:exists(S1_2066:exists(v_1994:exists(v_2064:(S1_1996= | 
  S1_1996=union(S1_2129,{v_2128})) & S=union(S1_2049,{v_2047}) & 
  S1=union(S1_1841,{v_1839}) & APP(S_1934,S1_1847,S2_1850) & S2=S2_1850 & 
  S1_1841=S1_1847 & v_1839=v_2047 & S_1934=union(S1_1996,{v_1994}) & 
  S1_2049=union(S1_2066,{v_2064}) & S1_2049=union(S1_2066,{v_2064}) & 
  S1_1996=S1_2066 & v_1994=v_2064))))))))))) --> APP(S,S1,S2),
 (exists(S1_1841:exists(v_1839:exists(S1_2151:exists(v_2149:S1_2151= & 
  S1_2151= & S_1922= & v_1839=v_2149 & S1_1841=S1_1847 & S2=S2_1850 & 
  APP(S_1922,S1_1847,S2_1850) & S1=union(S1_1841,{v_1839}) & S=union(S1_2151,
  {v_2149})))))) --> APP(S,S1,S2)]
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
!!! NEW RELS:[ (exists(S1_2270:exists(v_2268:exists(v_2572:exists(S1_2574:S=union(S1_2574,
  {v_2572}) & S1=union(S1_2270,{v_2268}) & APP1(S_2351,S1_2276,S2_2279) & 
  S2=S2_2279 & S1_2270=S1_2276 & v_2268=v_2572 & S1_2574=S_2351 & S_2351= & 
  S1_2574= & S1_2574=))))) --> APP1(S,S1,S2),
 (exists(S1_2455:exists(v_2454:(S2= | S2=union(S1_2455,{v_2454})) & S1= & 
  S2=S))) --> APP1(S,S1,S2),
 (exists(S1_2552:exists(v_2551:exists(S1_2270:exists(v_2268:exists(v_2470:exists(S1_2472:exists(S1_2422:exists(S1_2489:exists(v_2420:exists(v_2487:(S1_2422= | 
  S1_2422=union(S1_2552,{v_2551})) & S=union(S1_2472,{v_2470}) & 
  S1=union(S1_2270,{v_2268}) & APP1(S_2363,S1_2276,S2_2279) & S2=S2_2279 & 
  S1_2270=S1_2276 & v_2268=v_2470 & S_2363=union(S1_2422,{v_2420}) & 
  S1_2472=union(S1_2489,{v_2487}) & S1_2472=union(S1_2489,{v_2487}) & 
  S1_2422=S1_2489 & v_2420=v_2487))))))))))) --> APP1(S,S1,S2),
 (exists(S1_2270:exists(v_2268:exists(S1_2574:exists(v_2572:S1_2574= & 
  S1_2574= & S_2351= & S1_2574=S_2351 & v_2268=v_2572 & S1_2270=S1_2276 & 
  S2=S2_2279 & APP1(S_2351,S1_2276,S2_2279) & S1=union(S1_2270,{v_2268}) & 
  S=union(S1_2574,{v_2572})))))) --> APP1(S,S1,S2)]
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
!!! NEW RELS:[ (exists(v_2677:exists(v_2997:exists(S1_2679:exists(S1_2999:S=union(S1_2999,
  {v_2997}) & S1=union(S1_2679,{v_2677}) & S2= & S1_2999=S2 & 
  v_2677=v_2997 & S1_2679= & S1_2999= & S1_2999=))))) --> APP2(S,S1,S2),
 (exists(S1_2945:exists(v_2944:exists(v_2677:exists(v_2864:exists(v_2787:exists(S1_2789:exists(S1_2679:exists(S1_2866:exists(S1_2886:exists(v_2884:(S1_2789= | 
  S1_2789=union(S1_2945,{v_2944})) & S=union(S1_2866,{v_2864}) & 
  S1=union(S1_2679,{v_2677}) & S2=union(S1_2789,{v_2787}) & v_2677=v_2864 & 
  v_2787=v_2884 & S1_2789=S1_2886 & S1_2679= & S1_2866=union(S1_2886,
  {v_2884}) & S1_2866=union(S1_2886,{v_2884})))))))))))) --> APP2(S,S1,S2),
 (exists(S1_2679:exists(v_2677:exists(S1_2999:exists(v_2997:S1_2999= & 
  S1_2999= & S1_2679= & v_2677=v_2997 & S1_2999=S2 & S2= & S1=union(S1_2679,
  {v_2677}) & S=union(S1_2999,{v_2997})))))) --> APP2(S,S1,S2),
 (exists(S1_3152:exists(v_3151:exists(S1_2679:exists(v_2677:exists(S1_3103:exists(v_3101:S_3100=union(S1_3152,
  {v_3151}) & S_3100=S1_3103 & v_2677=v_3101 & S1_2679=S1_2798 & 
  S2=S2_2801 & APP2(S_3100,S1_2798,S2_2801) & S1=union(S1_2679,{v_2677}) & 
  S=union(S1_3103,{v_3101})))))))) --> APP2(S,S1,S2)]
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
!!! NEW RELS:[ (exists(S1_3324:exists(v_3322:S1_3324= & S1_3324= & v=v_3322 & 
  S=union(S1_3324,{v_3322})))) --> CL(S,v),
 (exists(S1_3420:exists(v_3419:exists(v_3342:exists(S1_3344:exists(S1_3319:exists(S1_3361:exists(v_3317:exists(v_3359:(S1_3319= | 
  S1_3319=union(S1_3420,{v_3419})) & S=union(S1_3344,{v_3342}) & 
  CL(S_3262,v) & v=v_3342 & S_3262=union(S1_3319,{v_3317}) & 
  S1_3344=union(S1_3361,{v_3359}) & S1_3344=union(S1_3361,{v_3359}) & 
  S1_3319=S1_3361 & v_3317=v_3359))))))))) --> CL(S,v)]
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
                                 Anon_67_3494=Anon_35 & S_3496=S4 & 
                                 n_230=n_197_3495 & n=n_197_3495 & 
                                 1<=n_197_3495 & 
                                 907::forall(_x:_x <notin> S_3496  | _x=v) & 
                                 0<=m&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
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
!!! NEW RELS:[ (exists(S1_4672:exists(v_4671:exists(S1_4577:exists(v:exists(v_4575:(S1_4577= | 
  S1_4577=union(S1_4672,{v_4671})) & S=union(S1_4577,{v_4575}) & (1+v)<=m & 
  v_4575=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_4577:exists(v_4575:v_4575<=v & S1_4577=S_4627 & 
  m_4686=m & (1+v)<=m & FGE(S_4627,m_4686) & S=union(S1_4577,
  {v_4575}))))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  GN(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[Anon_45; n; 
                    S](ex)x::dll<Anon_45,n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::ref [x]
                                EXISTS(flted_208_215,flted_208_216,Anon_46,
                                Anon_47,S1,
                                S2: x'::dll<Anon_46,flted_208_216,S1>@M[Orig][LHSCase] * 
                                res::dll<Anon_47,flted_208_215,S2>@M[Orig][LHSCase]&
                                flted_208_216=1 & flted_208_215+1=n & 
                                GN(S,S1,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_45; n; 
                  S](ex)x::dll<Anon_45,n,S>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 48::ref [x]
                              x'::dll<Anon_46,flted_208_216,S1>@M[Orig][LHSCase] * 
                              res::dll<Anon_47,flted_208_215,S2>@M[Orig][LHSCase]&
                              flted_208_216=1 & flted_208_215+1=n & union(S1,
                              S2)=S & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4791:exists(v_4790:exists(S1_4733:exists(v_4731:exists(v_4746:exists(S1_4748:(S1_4733= | 
  S1_4733=union(S1_4791,{v_4790})) & S1=union(S1_4748,{v_4746}) & 
  S=union(S1_4733,{v_4731}) & S1_4733=S2 & v_4731=v_4746 & S1_4748= & 
  S1_4748=))))))) --> GN(S,S1,S2)]
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
                                EXISTS(flted_254_207,Anon_64,
                                S2: res::dll<Anon_64,flted_254_207,S2>@M[Orig][LHSCase]&
                                flted_254_207+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_63; n; 
                  S](ex)x::dll<Anon_63,n,S>@M[Orig][LHSCase]&2<=n&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 62::
                              res::dll<Anon_64,flted_254_207,S2>@M[Orig][LHSCase]&
                              flted_254_207+2=n & S2<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4905:exists(v_4904:exists(v_4830:exists(S1_4832:exists(S1_4874:exists(v_4872:(S1_4874= | 
  S1_4874=union(S1_4905,{v_4904})) & S=union(S1_4832,{v_4830}) & 
  S1_4874=S2 & S1_4832=union(S1_4874,{v_4872})))))))) --> GNN(S,S2)]
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
!!! NEW RELS:[ (exists(S1_5037:exists(v_5035:exists(S1_4949:exists(v_4947:exists(S1_5020:exists(v_5018:S1_5037= & 
  S1_5020=union(S1_5037,{v_5035}) & S1_5020=union(S1_5037,{v_5035}) & 
  S1_4949= & v_4947=v_5018 & a=v_5035 & S=union(S1_4949,{v_4947}) & 
  S1=union(S1_5020,{v_5018})))))))) --> INSERT(S,S1,a),
 (exists(S1_5138:exists(v_5137:exists(S1_4949:exists(v_4947:exists(S1_5089:exists(v_5087:S1_5086=union(S1_5138,
  {v_5137}) & S1_5086=S1_5089 & v_4947=v_5087 & S1_4949=S_4989 & 
  INSERT(S_4989,S1_5086,a) & S=union(S1_4949,{v_4947}) & S1=union(S1_5089,
  {v_5087})))))))) --> INSERT(S,S1,a)]
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
!!! NEW RELS:[ (exists(S1_5191:exists(v_5550:exists(v_5189:exists(S1_5552:exists(S_178:exists(S1_5501:exists(v_5499:S2=union(S1_5552,
  {v_5550}) & S=union(S1_5191,{v_5189}) & CPY(S_5197,S2_5239) & 
  S_5197=S1_5191 & S1_5501=S1_5191 & v_5550=v_5499 & v_5189=v_5499 & 
  S1_5552=S2_5239 & S_5197= & S1_5501= & S1_5501= & S2_5239= & S1_5552= & 
  S1_5552= & S_178=union(S1_5501,{v_5499}))))))))) --> CPY(S,S2),
 (exists(S1_5191:exists(v_5550:exists(v_5189:exists(S1_5552:exists(S_178:exists(S1_5501:exists(v_5499:S2=union(S1_5552,
  {v_5550}) & S=union(S1_5191,{v_5189}) & CPY(S_5197,S2_5239) & 
  S_5197=S1_5191 & S1_5501=S1_5191 & v_5550=v_5499 & v_5189=v_5499 & 
  S1_5552=S2_5239 & S2_5239= & S_5197= & S1_5501= & S1_5501= & S1_5552= & 
  S1_5552= & S_178=union(S1_5501,{v_5499}))))))))) --> CPY(S,S2),
 (exists(S1_5191:exists(v_5583:exists(v_5189:exists(S1_5585:exists(S_178:exists(S1_5501:exists(v_5499:S2=union(S1_5585,
  {v_5583}) & S=union(S1_5191,{v_5189}) & CPY(S_5197,S2_5239) & 
  S_5197=S1_5191 & S1_5501=S1_5191 & v_5583=v_5499 & v_5189=v_5499 & 
  S1_5585=S2_5239 & S_5197= & S1_5501= & S1_5501= & S2_5239= & S1_5585= & 
  S1_5585= & S_178=union(S1_5501,{v_5499}))))))))) --> CPY(S,S2),
 (exists(S_178:S2= & S= & S_178=S & S_178= & S_178=)) --> CPY(S,S2),
 (exists(S1_5481:exists(v_5480:exists(S1_5191:exists(v_5389:exists(v_5189:exists(S1_5478:exists(v_5477:exists(S1_5391:exists(S_178:exists(S1_5331:exists(v_5329:exists(S1_5324:exists(S1_5411:exists(v_5322:exists(v_5409:(S1_5324= | 
  S1_5324=union(S1_5481,{v_5480})) & S2=union(S1_5391,{v_5389}) & 
  S=union(S1_5191,{v_5189}) & CPY(S_5197,S2_5239) & S1_5331=S1_5191 & 
  S_5197=S1_5191 & v_5389=v_5329 & v_5189=v_5329 & S_5197=union(S1_5478,
  {v_5477}) & S2_5239=union(S1_5324,{v_5322}) & S1_5391=union(S1_5411,
  {v_5409}) & S1_5391=union(S1_5411,{v_5409}) & S_178=union(S1_5331,
  {v_5329}) & S1_5324=S1_5411 & v_5322=v_5409)))))))))))))))) --> CPY(S,S2),
 (exists(S_178:exists(v_5499:exists(S1_5501:exists(S1_5191:exists(v_5189:exists(S1_5585:exists(v_5583:S_178=union(S1_5501,
  {v_5499}) & S1_5585= & S1_5585= & S1_5501= & S1_5501= & S2_5239= & 
  S_5197= & S1_5585=S2_5239 & v_5189=v_5499 & v_5583=v_5499 & 
  S1_5501=S1_5191 & S_5197=S1_5191 & CPY(S_5197,S2_5239) & S=union(S1_5191,
  {v_5189}) & S2=union(S1_5585,{v_5583}))))))))) --> CPY(S,S2),
 (exists(S_178:S_178= & S_178=S & S= & S2=)) --> CPY(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
 (exists(S1_7546:exists(v_7545:exists(S1_7462:exists(v_7460:exists(v_7498:exists(S1_7500:(S2_7497= | 
  S2_7497=union(S1_7546,{v_7545})) & S2=union(S1_7500,{v_7498}) & 
  S1=union(S1_7462,{v_7460}) & TRAV(S1_7468,S2_7497) & S1_7462=S1_7468 & 
  v_7460=v_7498 & S2_7497=S1_7500))))))) --> TRAV(S1,S2),
 (S2=S1 & S1= & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  true
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[Anon_39; m; 
                    S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(flted_113_224,Anon_40,
                                S2: x'::dll<Anon_40,flted_113_224,S2>@M[Orig][LHSCase]&
                                flted_113_224+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39; m; 
                  S1](ex)x::dll<Anon_39,m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              x'::dll<Anon_40,flted_113_224,S2>@M[Orig][LHSCase]&
                              flted_113_224+1=m & 0<=m&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(v_7616:exists(S1_7618:S2= & S1=union(S1_7618,{v_7616}) & 
  S2=S1_7618 & S1_7618=))) --> PF(S1,S2),
 (exists(S1_7618:exists(v_7616:S1_7618= & S2=S1_7618 & S1=union(S1_7618,
  {v_7616}) & S2=))) --> PF(S1,S2),
 (exists(S1_7777:exists(v_7776:exists(v_7616:exists(v_7721:exists(S1_7723:exists(S1_7618:exists(S1_7694:exists(v_7692:(S1_7694= | 
  S1_7694=union(S1_7777,{v_7776})) & S2=union(S1_7723,{v_7721}) & 
  S1=union(S1_7618,{v_7616}) & v_7692=v_7721 & S1_7694=S1_7723 & 
  S1_7618=union(S1_7694,{v_7692})))))))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
 (exists(S1_7943:exists(v_7942:exists(v_226:exists(v_7860:exists(v_7896:exists(S1_7862:exists(S1_7898:(S1_7862= | 
  S1_7862=union(S1_7943,{v_7942})) & S1=union(S1_7898,{v_7896}) & 
  S=union(S1_7862,{v_7860}) & v=v_226 & v_7860=v_7896 & 
  S1_7862=S1_7898)))))))) --> PUF(S1,S,v)]
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

Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
!!! NEW RELS:[ (exists(v_8756:exists(S1_8758:S2=union(S1_8758,{v_8756}) & S= & S1_8758=S & 
  v=v_8756 & S1_8758= & S1_8758=))) --> SN(S,S2,v),
 (exists(v_8756:exists(S1_8758:S2=union(S1_8758,{v_8756}) & S= & S1_8758=S & 
  v=v_8756 & S1_8758= & S1_8758=))) --> SN(S,S2,v),
 (exists(S1_8901:exists(v_8900:exists(v_8820:exists(v_8752:exists(S1_8754:exists(S1_8822:exists(S1_8842:exists(v_8840:(S1_8754= | 
  S1_8754=union(S1_8901,{v_8900}) | S1_8754= | S1_8754=union(S1_8901,
  {v_8900})) & S2=union(S1_8822,{v_8820}) & S=union(S1_8754,{v_8752}) & 
  v=v_8820 & v_8752=v_8840 & S1_8754=S1_8842 & S1_8822=union(S1_8842,
  {v_8840}) & S1_8822=union(S1_8842,{v_8840})))))))))) --> SN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

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
!!! NEW RELS:[ (exists(S1_10003:exists(v_10002:exists(S1_9853:exists(v_9851:exists(S1_9962:exists(v_9960:S1_9962= & 
  S1_9962= & S1_9853=union(S1_10003,{v_10002}) & v_9851=v_9960 & 
  S1_9853=S2 & S=union(S1_9853,{v_9851}) & S1=union(S1_9962,
  {v_9960})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_10125:exists(v_10124:exists(S1_10128:exists(v_10127:exists(S1_9903:exists(v_9901:exists(S1_10024:exists(v_10022:S1_10018=union(S1_10125,
  {v_10124}) & S2_10019=union(S1_10128,{v_10127}) & S1_10018=S1_10024 & 
  v_9901=v_10022 & S1_9903=S_9906 & S2_10019=S2 & 
  SPLIT(S_9906,S1_10018,S2_10019) & S=union(S1_9903,{v_9901}) & 
  S1=union(S1_10024,{v_10022})))))))))) --> SPLIT(S,S1,S2)]
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


21 false contexts at: ( (542,6)  (238,13)  (238,4)  (341,4)  (341,11)  (351,6)  (351,13)  (350,6)  (350,6)  (348,6)  (348,13)  (347,8)  (346,27)  (346,14)  (346,9)  (345,10)  (345,4)  (344,8)  (344,12)  (344,4)  (344,4) )

Total verification time: 48.29 second(s)
	Time spent in main process: 7.68 second(s)
	Time spent in child processes: 40.61 second(s)
