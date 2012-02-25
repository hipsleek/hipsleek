/usr/local/bin/mona

Processing file "sll_msb.ss"
Parsing sll_msb.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FGE(S,m)
!!! POST:  {m}<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FGE]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&0<=n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 80::
                                
                                true&res=null&{FLOW,(20,21)=__norm}
                                or EXISTS(Anon_18,
                                   m: res::node<m,Anon_18>@M[Orig]&v<=m & 
                                   FGE(S,m)&{FLOW,(20,21)=__norm})
                                )
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  0<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 80::
                              
                              true&res=null & 0<=n&{FLOW,(20,21)=__norm}
                              or res::node<m,Anon_18>@M[Orig]&v<=m & 
                                 {m}<subset> S  & 0<=n&{FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[ (exists(S1_2098:exists(v_2096:exists(S1_2009:exists(v:exists(v_2006:(S1_2009= | 
  S1_2009=union(S1_2098,{v_2096})) & S=union(S1_2009,{v_2006}) & v<=m & 
  v_2006=m)))))) --> FGE(S,m),
 (exists(v:exists(S1_2009:exists(v_2006:(1+v_2006)<=v & S1_2009=S_2056 & 
  m_2108=m & v<=m & FGE(S_2056,m_2108) & S=union(S1_2009,
  {v_2006}))))) --> FGE(S,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(S,S2,v)
!!! POST:  S=union(S2,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::ref [x]
                                EXISTS(flted_131_109,flted_131_110,S2,
                                v: x'::node<v,flted_131_110>@M[Orig] * 
                                res::sll1<flted_131_109,S2>@M[Orig][LHSCase]&
                                flted_131_110=null & flted_131_109+1=n & 
                                GN(S,S2,v)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              x'::node<v,flted_131_110>@M[Orig] * 
                              res::sll1<flted_131_109,S2>@M[Orig][LHSCase]&
                              flted_131_110=null & flted_131_109+1=n & 
                              S=union(S2,{v}) & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2180:exists(v_2178:exists(S1_2151:exists(v_2148:(S1_2151= | 
  S1_2151=union(S1_2180,{v_2178})) & S=union(S1_2151,{v_2148}) & 
  S1_2151=S2 & v_2148=v))))) --> GN(S,S2,v)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! REL :  GNN(S,S2)
!!! POST:  S2<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GNN]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&1<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 37::
                                EXISTS(flted_185_99,
                                S2: res::sll1<flted_185_99,S2>@M[Orig][LHSCase]&
                                flted_185_99+2=n & GNN(S,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  2<=n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              res::sll1<flted_185_99,S2>@M[Orig][LHSCase]&
                              flted_185_99+2=n & S2<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2270:exists(v_2268:exists(v_2208:exists(S1_2211:exists(S1_2241:exists(v_2238:(S1_2241= | 
  S1_2241=union(S1_2270,{v_2268})) & S=union(S1_2211,{v_2208}) & 
  S1_2241=S2 & S1_2211=union(S1_2241,{v_2238})))))))) --> GNN(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(S,S1)
!!! POST:  S1<subset> S 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(flted_167_103,
                                S1: res::sll1<flted_167_103,S1>@M[Orig][LHSCase]&
                                flted_167_103+1=n & GT(S,S1)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              res::sll1<flted_167_103,S1>@M[Orig][LHSCase]&
                              flted_167_103+1=n & S1<subset> S  & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_2333:exists(v_2331:exists(v_2302:exists(S1_2305:(S1_2305= | 
  S1_2305=union(S1_2333,{v_2331})) & S=union(S1_2305,{v_2302}) & 
  S1_2305=S1))))) --> GT(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  CPY(S,S1)
!!! POST:  S1=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [CPY]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 69::
                                EXISTS(n_84,S_85,n_86,
                                S1: x::sll1<n_84,S_85>@M[Orig][LHSCase] * 
                                res::sll1<n_86,S1>@M[Orig][LHSCase]&
                                CPY(S,S1) & n_84=n & S_85=S & n_86=n&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 69::
                              x::sll1<n_84,S_85>@M[Orig][LHSCase] * 
                              res::sll1<n_86,S1>@M[Orig][LHSCase]&n_84=n & 
                              S_85=S & n_86=n & S1=S & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S_85:S1= & S= & S_85=S & S_85= & S_85=)) --> CPY(S,S1),
 (exists(S1_3035:exists(v_3033:exists(S1_3032:exists(v_3030:exists(S1_2899:exists(v_2986:exists(v_2896:exists(S1_2989:exists(S_85:exists(S1_2946:exists(v_2943:(S_2903= & 
  S1_2938= | S1_2938=union(S1_3035,{v_3033}) & S_2903=union(S1_3032,
  {v_3030})) & S1=union(S1_2989,{v_2986}) & S=union(S1_2899,{v_2896}) & 
  CPY(S_2903,S1_2938) & S1_2946=S1_2899 & S_2903=S1_2899 & v_2986=v_2943 & 
  v_2896=v_2943 & S1_2938=S1_2989 & S_85=union(S1_2946,
  {v_2943}))))))))))))) --> CPY(S,S1),
 (exists(S_85:S_85= & S_85=S & S= & S1=)) --> CPY(S,S1)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  FIL(S,S2)
!!! POST:  S=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [FIL]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::
                                EXISTS(m,
                                S2: res::sll1<m,S2>@M[Orig][LHSCase]&m<=n & 
                                FIL(S,S2)&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              res::sll1<m,S2>@M[Orig][LHSCase]&m<=n & S=S2 & 
                              0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S= & S2=S) --> FIL(S,S2),
 (exists(m_3125:exists(n_3187:exists(res:exists(v_node_346_719':exists(tmp_83':exists(m_3231:exists(m:exists(m_3238:exists(m_3270:exists(n:exists(v_bool_335_717':exists(v:exists(r_3237:exists(x:exists(v_bool_334_718':exists(S1_3271:exists(v_3269:exists(S1_3239:exists(v_3236:exists(S1_3126:exists(v_3123:(S2_3232= & 
  (S1_3126=S_3188 & 1+m_3125=n & 1+n_3187=n & res=x & v_node_346_719'=x & 
  v_3123=v_3236 & tmp_83'=r_3237 & m_3231=0 & S2_3232=S1_3239 & m=1 & 
  m_3238=0 & (1+v)<=v_3236 & !(v_bool_335_717') & r_3237=null & x!=null & 
  1<=n & v_bool_334_718' & FIL(S_3188,S2_3232) | S1_3126=S_3188 & 1+
  m_3125=n & 1+n_3187=n & res=x & v_node_346_719'=x & v_3123=v_3236 & 
  tmp_83'=r_3237 & m_3231=0 & S2_3232=S1_3239 & m=1 & m_3238=0 & 
  !(v_bool_335_717') & r_3237=null & (1+v_3236)<=v & x!=null & 1<=n & 
  v_bool_334_718' & FIL(S_3188,S2_3232)) | (S1_3126=S_3188 & 1+m_3125=n & 1+
  n_3187=n & res=x & v_node_346_719'=x & v_3123=v_3236 & tmp_83'=r_3237 & -1+
  m_3231=m_3270 & S2_3232=S1_3239 & -2+m=m_3270 & -1+m_3238=m_3270 & 
  0<=m_3270 & (2+m_3270)<=n & (1+v)<=v_3236 & !(v_bool_335_717') & 
  r_3237!=null & x!=null & v_bool_334_718' & FIL(S_3188,S2_3232) | 
  S1_3126=S_3188 & 1+m_3125=n & 1+n_3187=n & res=x & v_node_346_719'=x & 
  v_3123=v_3236 & tmp_83'=r_3237 & -1+m_3231=m_3270 & S2_3232=S1_3239 & -2+
  m=m_3270 & -1+m_3238=m_3270 & 0<=m_3270 & (2+m_3270)<=n & 
  !(v_bool_335_717') & (1+v_3236)<=v & r_3237!=null & x!=null & 
  v_bool_334_718' & FIL(S_3188,S2_3232)) & S2_3232=union(S1_3271,
  {v_3269})) & S2=union(S1_3239,{v_3236}) & S=union(S1_3126,
  {v_3123}))))))))))))))))))))))) --> FIL(S,S2),
 (S2=S & S= & S2=) --> FIL(S,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
!!! REL :  TRAV(S1,S2)
!!! POST:  S1=S2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [TRAV]
              EBase exists (Expl)(Impl)[n; 
                    S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 66::
                                EXISTS(n_88,
                                S2: x::sll1<n_88,S2>@M[Orig][LHSCase]&
                                TRAV(S1,S2) & n_88=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  S1](ex)x::sll1<n,S1>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 66::
                              x::sll1<n_88,S2>@M[Orig][LHSCase]&n_88=n & 
                              S1=S2 & 0<=n&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (S2= & S1= & S2=S1) --> TRAV(S1,S2),
 (exists(S1_3437:exists(v_3435:exists(S1_3373:exists(v_3370:exists(v_3405:exists(S1_3408:(S2_3404= | 
  S2_3404=union(S1_3437,{v_3435})) & S2=union(S1_3408,{v_3405}) & 
  S1=union(S1_3373,{v_3370}) & TRAV(S1_3377,S2_3404) & S1_3373=S1_3377 & 
  v_3370=v_3405 & S2_3404=S1_3408))))))) --> TRAV(S1,S2),
 (S2=S1 & S1= & S2=) --> TRAV(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(S1,S2)
!!! POST:  S2<subset> S1 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; 
                    S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_92_115,
                                S2: x'::sll1<flted_92_115,S2>@M[Orig][LHSCase]&
                                flted_92_115+1=m & PF(S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  S1](ex)x::sll1<m,S1>@M[Orig][LHSCase]&x!=null&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              x'::sll1<flted_92_115,S2>@M[Orig][LHSCase]&
                              flted_92_115+1=m & S2<subset> S1  & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4063:exists(v_4061:exists(v_4031:exists(S1_4034:(S1_4034= | 
  S1_4034=union(S1_4063,{v_4061})) & S1=union(S1_4034,{v_4031}) & 
  S1_4034=S2))))) --> PF(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SN(S,S2,v)
!!! POST:  S2=union(S,{v})
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SN]
              EBase exists (Expl)(Impl)[v; t; Anon_15; Anon_16; j; 
                    S](ex)x::node<v,t>@M[Orig] * 
                    t::sll1<Anon_15,Anon_16>@M[Orig][LHSCase] * 
                    y::sll1<j,S>@M[Orig][LHSCase]&x!=null&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::ref [x]
                                EXISTS(k,S2: x::sll1<k,S2>@M[Orig][LHSCase]&
                                1<=k & k=1+j & SN(S,S2,v)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[v; t; Anon_15; Anon_16; j; 
                  S](ex)x::node<v,t>@M[Orig] * 
                  t::sll1<Anon_15,Anon_16>@M[Orig][LHSCase] * 
                  y::sll1<j,S>@M[Orig][LHSCase]&x!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 28::ref [x]
                              x::sll1<k,S2>@M[Orig][LHSCase]&1<=k & k=1+j & 
                              S2=union(S,{v}) & 0<=Anon_15 & 0<=j&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4160:exists(v_4158:exists(S1_4126:exists(v_4123:(S= | 
  S=union(S1_4160,{v_4158}) | S= | S=union(S1_4160,{v_4158})) & 
  S2=union(S1_4126,{v_4123}) & S=S1_4126 & v=v_4123))))) --> SN(S,S2,v)]
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

Checking procedure split1$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  SPLIT(S,S1,S2)
!!! POST:  union(S1,S2)=S
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SPLIT]
              EBase exists (Expl)(Impl)[n; 
                    S](ex)x::sll1<n,S>@M[Orig][LHSCase]&0<a & a<n&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 83::ref [x]
                                EXISTS(n1,n2,S1,
                                S2: x'::sll1<n1,S1>@M[Orig][LHSCase] * 
                                res::sll1<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                                0<n1 & 0<n2 & SPLIT(S,S1,S2)&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S](ex)x::sll1<n,S>@M[Orig][LHSCase]&
                  1<=a & a<n&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 83::ref [x]
                              x'::sll1<n1,S1>@M[Orig][LHSCase] * 
                              res::sll1<n2,S2>@M[Orig][LHSCase]&n=n2+n1 & 
                              0<n1 & 0<n2 & union(S1,S2)=S & 0<=n&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (exists(S1_4550:exists(v_4548:exists(S1_4425:exists(v_4422:exists(S1_4521:exists(v_4518:S1_4521= & 
  S1_4521= & S1_4425=union(S1_4550,{v_4548}) & v_4422=v_4518 & S1_4425=S2 & 
  S=union(S1_4425,{v_4422}) & S1=union(S1_4521,
  {v_4518})))))))) --> SPLIT(S,S1,S2),
 (exists(S1_4664:exists(v_4662:exists(S1_4667:exists(v_4665:exists(S1_4465:exists(v_4462:exists(S1_4572:exists(v_4569:S1_4565=union(S1_4664,
  {v_4662}) & S2_4566=union(S1_4667,{v_4665}) & S1_4565=S1_4572 & 
  v_4462=v_4569 & S1_4465=S_4467 & S2_4566=S2 & 
  SPLIT(S_4467,S1_4565,S2_4566) & S=union(S1_4465,{v_4462}) & 
  S1=union(S1_4572,{v_4569})))))))))) --> SPLIT(S,S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n; S1; m; 
                    S2](ex)x::sll1<n,S1>@M[Orig][LHSCase] * 
                    y::sll1<m,S2>@M[Orig][LHSCase]&0<=n & 0<=m&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 13::ref [x;y]
                                EXISTS(m_120,n_121,S3,
                                S4: x'::sll1<m_120,S3>@M[Orig][LHSCase] * 
                                y'::sll1<n_121,S4>@M[Orig][LHSCase]&
                                m_120=m & n_121=n&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; S1; m; 
                  S2](ex)x::sll1<n,S1>@M[Orig][LHSCase] * 
                  y::sll1<m,S2>@M[Orig][LHSCase]&0<=n & 0<=m&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 13::ref [x;y]
                              x'::sll1<m_120,S3>@M[Orig][LHSCase] * 
                              y'::sll1<n_121,S4>@M[Orig][LHSCase]&y=x' & 
                              y'=x & S2=S3 & S1=S4 & m=m_120 & n=n_121 & 
                              0<=n_121 & 0<=m_120 & 0<=n & 0<=m&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure swap$node~node SUCCESS

Termination checking result:


20 false contexts at: ( (159,13)  (159,4)  (339,10)  (339,6)  (338,10)  (338,6)  (36,17)  (36,24)  (37,7)  (37,14)  (286,4)  (286,11)  (291,4)  (291,11)  (290,10)  (290,4)  (289,9)  (289,13)  (289,4)  (289,4) )

Total verification time: 9.56 second(s)
	Time spent in main process: 2.24 second(s)
	Time spent in child processes: 7.32 second(s)
