
Processing file "sll_mso.ss"
Parsing sll_mso.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure delete$node~int... 
Procedure delete$node~int SUCCESS

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! REL :  GN(sres,xs,lres,xl)
!!! POST:  sres>=xs & lres>=sres & xl>=lres
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GN]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 26::ref [x]
                                EXISTS(flted_143_112,flted_143_113,lres,v,
                                sres: x'::node<v,flted_143_113>@M[Orig][] * 
                                res::sll2<flted_143_112,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([null=flted_143_113]
                                 [0<=flted_143_112 & 1+flted_143_112=n]
                                 [sres<=lres & v<=sres & xs<=v & 
                                   GN(sres,xs,lres,xl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 26::ref [x]
                              EXISTS(flted_143_1971,flted_143_1972,lres_1973,
                              v_1974,
                              sres_1975: x'::node<v_1974,flted_143_1972>@M[Orig][] * 
                              res::sll2<flted_143_1971,sres_1975,lres_1973>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lres_1973<=xl & xs<=xl & v_1974<=sres_1975 & 
                                 xs<=sres_1975 & sres_1975<=lres_1973 & 
                                 xs<=v_1974]
                               [x'!=null]
                               [0<=flted_143_1971 & 0<=n & 1+flted_143_1971=n]
                               [null=flted_143_1972]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qmin_1958:sres<=lres & lres<=xl & xs<=qmin_1958 & 
  qmin_1958<=sres)) --> GN(sres,xs,lres,xl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=1]
!!! REL :  GNN(sm1,lg1,sm2,lg2)
!!! POST:  sm2>=sm1 & lg2>=sm2 & lg1>=lg2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [n,GNN]
              EBase exists (Expl)(Impl)[n; sm1; 
                    lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                    (([null!=x][0<=n & 0!=n][sm1<=lg1]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(flted_206_102,sm2,
                                lg2: res::sll2<flted_206_102,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_206_102 & 2+flted_206_102=n]
                                 [sm2<=lg2 & GNN(sm1,lg1,sm2,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; sm1; 
                  lg1](ex)x::sll2<n,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=n][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][2<=n | n<=0]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 38::
                              EXISTS(flted_206_2041,sm2_2042,
                              lg2_2043: res::sll2<flted_206_2041,sm2_2042,lg2_2043>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lg2_2043<=lg1 & sm1<=lg1 & sm1<=sm2_2042 & 
                                 sm2_2042<=lg2_2043]
                               [0<=flted_206_2041 & 0<=n & 2+flted_206_2041=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(qs_1998:sm2<=lg2 & 
  exists(qmin_2000:exists(qmin_2033:exists(ql_1999:qs_1998<=qmin_2033 & 
  qmin_2000<=qs_1998 & sm1<=qmin_2000 & qmin_2033<=sm2 & lg2<=ql_1999 & 
  ql_1999<=lg1))))) --> GNN(sm1,lg1,sm2,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure get_tail$node... 
!!! REL :  GT(sres,xs,lres,xl)
!!! POST:  sres>=xs & lres>=sres & xl>=lres
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [GT]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_186_106,sres,
                                lres: res::sll2<flted_186_106,sres,lres>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_186_106 & 1+flted_186_106=n]
                                 [sres<=lres & GT(sres,xs,lres,xl)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(flted_186_2076,sres_2077,
                              lres_2078: res::sll2<flted_186_2076,sres_2077,lres_2078>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lres_2078<=xl & xs<=xl & xs<=sres_2077 & 
                                 sres_2077<=lres_2078]
                               [0<=flted_186_2076 & 0<=n & 1+flted_186_2076=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sres<=lres & lres<=xl & exists(qmin_2068:xs<=qmin_2068 & 
  qmin_2068<=sres)) --> GT(sres,xs,lres,xl)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_tail$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Checking procedure insert2$node~node... 
Procedure insert2$node~node SUCCESS

Checking procedure list_copy$node... 
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
Procedure list_filter2$node~int SUCCESS

Checking procedure list_traverse$node... 
Procedure list_traverse$node SUCCESS

Checking procedure merge1$node~node... 
Procedure merge1$node~node SUCCESS

Checking procedure pop_front$node... 
!!! REL :  PF(sm1,sm2,lg1,lg2)
!!! POST:  sm2>=sm1 & lg2>=sm2 & lg1>=lg2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [PF]
              EBase exists (Expl)(Impl)[m; sm1; 
                    lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                    (([null!=x][0<=m & 0!=m][sm1<=lg1]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 18::ref [x]
                                EXISTS(flted_104_118,sm2,
                                lg2: x'::sll2<flted_104_118,sm2,lg2>@M[Orig][LHSCase]@ rem br[{384,383}]&
                                (
                                ([0<=flted_104_118 & 1+flted_104_118=m]
                                 [sm2<=lg2 & PF(sm1,sm2,lg1,lg2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; sm1; 
                  lg1](ex)x::sll2<m,sm1,lg1>@M[Orig][LHSCase]@ rem br[{383}]&
                  (([x!=null][1<=m][sm1<=lg1]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 18::ref [x]
                              EXISTS(flted_104_3023,sm2_3024,
                              lg2_3025: x'::sll2<flted_104_3023,sm2_3024,lg2_3025>@M[Orig][LHSCase]@ rem br[{384,383}]&
                              (
                              ([lg2_3025<=lg1 & sm1<=lg1 & sm1<=sm2_3024 & 
                                 sm2_3024<=lg2_3025]
                               [0<=flted_104_3023 & 0<=m & 1+flted_104_3023=m]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (sm2<=lg2 & lg2<=lg1 & exists(qmin_3010:sm1<=qmin_3010 & 
  qmin_3010<=sm2)) --> PF(sm1,sm2,lg1,lg2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Procedure push_front$node~int SUCCESS

Checking procedure set_next$node~node... 
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! REL :  SNULL(xs,v,sl_3127)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [x]
                                EXISTS(flted_196_104,v,
                                sl: x'::node<v,flted_196_104>@M[Orig][]&(
                                ([null=flted_196_104][SNULL(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [x]
                              EXISTS(flted_196_3128,
                              v_3129: x'::node<v_3129,flted_196_3128>@M[Orig][]&
                              (
                              ([x'!=null][null=flted_196_3128][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(xl:exists(ql_3123:ql_3123<=xl & xs<=v & 
  exists(qs_3122:qs_3122<=ql_3123 & v<=qs_3122)))) --> SNULL(xs,v,sl_3127)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! REL :  SNULL2(xs,v,sl_3170)
!!! POST:  v>=xs
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [SNULL2]
              EBase exists (Expl)(Impl)[n; xs; 
                    xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                    ([null!=x][0<=n & 0!=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [x]
                                EXISTS(flted_173_108,v,
                                sl: x'::node<v,flted_173_108>@M[Orig][]&(
                                ([null=flted_173_108][SNULL2(xs,v,sl)]
                                 [x'!=null]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; xs; 
                  xl](ex)x::sll2<n,xs,xl>@M[Orig][LHSCase]@ rem br[{383}]&(
                  ([x!=null][1<=n][xs<=xl]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              EXISTS(flted_173_3171,
                              v_3172: x'::node<v_3172,flted_173_3171>@M[Orig][]&
                              (
                              ([x'!=null][null=flted_173_3171][0<=n][xs<=xl]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(xl:exists(ql_3162:ql_3162<=xl & xs<=v & 
  exists(qs_3161:qs_3161<=ql_3162 & v<=qs_3161)))) --> SNULL2(xs,v,sl_3170)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure split1$node~int... 
( [(185::,1 ); (185::,1 )]) :sll_mso.ss:320: 10: Postcondition cannot be derived from context


(Cause of PostCond Failure):sll_mso.ss:320: 10:  List of Partial Context: [PC(1, 0)]
Failed States:
[
 Label: [(185::,1 ); (185::,1 )]
 State:
        
         fe_kind: MAY
         fe_name: logical bug
         fe_locs: {
                   fc_message: 
                    (failure_code=213)  sl_3313=ql_3308 & qs_3307=sm_3312 & qs_3307<=ql_3308 & ql_3308<=sl & 
sm<=sl & sm<=qmin_3309 & qmin_3309<=qs_3307 & sm1_3390<=sl1_3391 & 
qmin_3403=qmin_3309 |-  qmin_3403<=sm1_3390 (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
         Trivial fail : MUSTno lemma found in both LHS and RHS nodes (do coercion)
       
 ]
Successful States:


Context of Verification Failure: File "sll_mso.ss",Line:320,Col:10
Last Proving Location: File "sll_mso.ss",Line:334,Col:12

ERROR: at sll_mso.ss_320_10 
Message: Post condition cannot be derived by the system.
 
Procedure split1$node~int FAIL-2

Exception Failure("Post condition cannot be derived by the system.") Occurred!

Error(s) detected when checking procedure split1$node~int

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1442 invocations 
16 false contexts at: ( (178,13)  (178,4)  (35,17)  (35,24)  (36,7)  (36,14)  (307,4)  (307,11)  (312,4)  (312,11)  (311,10)  (311,4)  (310,9)  (310,13)  (310,4)  (310,4) )

Total verification time: 2.44 second(s)
	Time spent in main process: 2.13 second(s)
	Time spent in child processes: 0.31 second(s)
