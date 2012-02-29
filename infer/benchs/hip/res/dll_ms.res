
Processing file "dll_ms.ss"
Parsing dll_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[q; 
                    p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                    y::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::
                                EXISTS(q_164: x::dll<q_164>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([q=q_164]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; 
                  p](ex)x::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                  y::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 29::
                              EXISTS(q_1443: x::dll<q_1443>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][q=q_1443]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
( [(364::,0 ); (364::,0 )]) :dll_ms.ss:243: 10: bind: node  v_node_243_972'::node<val_243_973',prev_243_974',next_243_975'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):dll_ms.ss:243: 10:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(364::,0 ); (364::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    (failure_code=15.3)  v_node_243_972'=q_1598 & v_node_243_972'=null |-  v_node_243_972'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 54::
                                EXISTS(p_159: x::dll<p_159>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_159]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 54::
                              EXISTS(p_1679: x::dll<p_1679>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([p=p_1679]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete$node~int result FAIL-1

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
!!! REL :  A(x')
!!! POST:  x'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&(([A(x')]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              true&(([null=x']))&{FLOW,(20,21)=__norm})
!!! NEW RELS:[ (x'=null) --> A(x')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure delete_list$node SUCCESS

Checking procedure empty$node... 
!!! REL :  EMPT1(res)
!!! POST:  res
!!! PRE :  true
!!! REL :  EMPT2(res)
!!! POST:  !(res)
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [EMPT1,EMPT2]
              EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      ECase case {
                             x=null -> ((None,[]),EBase true&MayLoop&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 4::
                                                            true&(
                                                            ([EMPT1(res)]))&
                                                            {FLOW,(20,21)=__norm})
                             ;
                             x!=null -> ((None,[]),EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 5::
                                                             true&(
                                                             ([EMPT2(res)]))&
                                                             {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    ECase case {
                           x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 4::
                                                          true&(
                                                          ([res][null=x]))&
                                                          {FLOW,(20,21)=__norm})
                           ;
                           x!=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 5::
                                                           true&(
                                                           ([!(res)][
                                                            x!=null]))&
                                                           {FLOW,(20,21)=__norm})
                           
                           })
!!! NEW RELS:[ (1<=res) --> EMPT1(res),
 (res<=0) --> EMPT2(res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure empty$node SUCCESS

Checking procedure find_ge$node~int... 
Procedure find_ge$node~int SUCCESS

Checking procedure front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              EXISTS(Anon_2064,p_2065,q_2066,
                              self_2067: self_2067::node<Anon_2064,p_2065,q_2066>@M[Orig][] * 
                              q_2066::dll<self_2067>@M[Orig]@ rem br[{529,528}]&
                              (
                              ([x=self_2067 & self_2067!=null]
                               [Anon_19=p_2065][res=Anon_2064]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_32](ex)x::dll<Anon_32>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_32](ex)x::dll<Anon_32>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(q_2103,self_2104,f_2105,Anon_2106,
                              next_169_2107: q_2103::dll<self_2104>@M[Orig]@ rem br[{529,528}] * 
                              self_2104::node<Anon_2106,prev_169_1108',next_169_2107>@M[Orig][]&
                              (
                              ([x=self_2104 & self_2104!=null]
                               [null=next_169_2107][null=prev_169_1108']
                               [res=q_2103]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_42](ex)x::dll<Anon_42>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 49::
                                EXISTS(Anon_43: res::dll<Anon_43>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_42](ex)x::dll<Anon_42>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 49::
                              
                              EXISTS(p_2174,Anon_2175,p_2176,q_2177,
                              Anon_2178: p_2174::node<Anon_2175,p_2176,q_2177>@M[Orig][] * 
                              res::dll<Anon_2178>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (
                              ([Anon_2178=q_2177 & q_2177!=null]
                               [x=p_2174 & x!=null][Anon_42=p_2176]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(self_2179,Anon_2180,p_2181,
                                 q_2182: self_2179::node<Anon_2180,p_2181,q_2182>@M[Orig][]&
                                 (
                                 ([x=self_2179 & self_2179!=null][null=res]
                                  [null=q_2182][Anon_42=p_2181]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next_next$node SUCCESS

Checking procedure insert$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::
                                EXISTS(p_162: x::dll<p_162>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_162]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 51::
                              EXISTS(p_2276: x::dll<p_2276>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][p=p_2276]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure list_copy$node... 
Procedure list_copy$node SUCCESS

Checking procedure list_filter2$node~int... 
Procedure list_filter2$node~int SUCCESS

Checking procedure list_remove$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 99::
                                EXISTS(p_138: x::dll<p_138>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_138]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 99::
                              EXISTS(p_2870: x::dll<p_2870>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][p=p_2870]))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure list_remove$node~int SUCCESS

Checking procedure list_remove2$node~int... 
Procedure list_remove2$node~int SUCCESS

Checking procedure list_traverse$node... 
Procedure list_traverse$node SUCCESS

Checking procedure pop_front$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_28](ex)x::dll<Anon_28>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::ref [x]
                                EXISTS(Anon_29: x'::dll<Anon_29>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_28](ex)x::dll<Anon_28>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 22::ref [x]
                              
                              EXISTS(tmp_3236,f_3237,Anon_3238,
                              p_3239: tmp_3236::node<Anon_3238,p_3239,next_120_1156'>@M[Orig][]&
                              (
                              ([res=x & res=tmp_3236 & res!=null][null=x']
                               [null=next_120_1156'][Anon_28=p_3239]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(tmp_3240,f_3241,Anon_3242,p_3243,
                                 Anon_3244: tmp_3240::node<Anon_3242,p_3243,next_127_1172'>@M[Orig][] * 
                                 x'::dll<Anon_3244>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                 (
                                 ([res=x & res=tmp_3240 & res!=null]
                                  [x'!=null][null=next_127_1172']
                                  [Anon_28=p_3243][Anon_3244=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure pop_front$node SUCCESS

Checking procedure push_front$node~int... 
Procedure push_front$node~int SUCCESS

Checking procedure ret_first$node... 
Procedure ret_first$node SUCCESS

Checking procedure reverse$node~node... 
!!! REL :  REVERSE(xs')
!!! POST:  xs'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [REVERSE]
              EBase exists (Expl)(Impl)[p; 
                    q](ex)xs::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                    ys::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 76::ref [xs;ys]
                                EXISTS(Anon_47: ys'::dll<Anon_47>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([REVERSE(xs')]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; 
                  q](ex)xs::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                  ys::dll<q>@M[Orig][LHSCase]@ rem br[{529,528}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 76::ref [xs;ys]
                              EXISTS(Anon_3492: ys'::dll<Anon_3492>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([null=xs']))&{FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (xs'=null) --> REVERSE(xs')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_33; 
                    Anon_34](ex)x::dll<Anon_33>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                    y::dll<Anon_34>@M[Orig][LHSCase]@ rem br[{529,528}]&(
                    ())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                EXISTS(Anon_35: x::dll<Anon_35>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (())&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_33; 
                  Anon_34](ex)x::dll<Anon_33>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                  y::dll<Anon_34>@M[Orig][LHSCase]@ rem br[{529,528}]&(
                  ())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              
                              EXISTS(Anon_3620: x::dll<Anon_3620>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (([x!=null][null=y][Anon_3620=Anon_33]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(Anon_3621: x::dll<Anon_3621>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                 (([y!=null][x!=null][Anon_3621=Anon_33]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_39](ex)x::dll<Anon_39>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(Anon_40,Anon_41,
                                r: x::node<Anon_40,Anon_41,r>@M[Orig][]&(
                                ([x!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_39](ex)x::dll<Anon_39>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(Anon_3644,Anon_3645,
                              r_3646: x::node<Anon_3644,Anon_3645,r_3646>@M[Orig][]&
                              (([x!=null][null=r_3646][Anon_39=Anon_3645]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_36](ex)x::dll<Anon_36>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::
                                EXISTS(Anon_37,Anon_38,
                                r: x::node<Anon_37,Anon_38,r>@M[Orig][]&(
                                ([x!=null]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_36](ex)x::dll<Anon_36>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 43::
                              EXISTS(Anon_3680,Anon_3681,
                              r_3682: x::node<Anon_3680,Anon_3681,r_3682>@M[Orig][]&
                              (([x!=null][null=r_3682][Anon_3681=Anon_36]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null2$node SUCCESS

Checking procedure size_helper$node~int... 
Procedure size_helper$node~int SUCCESS

Checking procedure size$node... 
Procedure size$node SUCCESS

Checking procedure splice$node~node... 
Procedure splice$node~node SUCCESS

Checking procedure split1$node~int... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                    (([1<=a]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 84::ref [x]
                                EXISTS(p_145,
                                Anon_48: x'::dll<p_145>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                                res::dll<Anon_48>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                (([p=p_145]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]@ rem br[{529,528}]&
                  (([1<=a]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 84::ref [x]
                              
                              EXISTS(p_4057,
                              Anon_4058: x'::dll<p_4057>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                              res::dll<Anon_4058>@M[Orig][LHSCase]@ rem br[{529,528}]&
                              (
                              ([x'=x & Anon_4058=x' & x'!=null][p=p_4057]
                               [1=a]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(p_4059,
                                 Anon_4060: x'::dll<p_4059>@M[Orig][LHSCase]@ rem br[{529,528}] * 
                                 res::dll<Anon_4060>@M[Orig][LHSCase]@ rem br[{529,528}]&
                                 (([2<=a][x'=x & x'!=null][p=p_4059]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1166 invocations 
7 false contexts at: ( (491,10)  (196,13)  (196,4)  (44,4)  (44,11)  (46,4)  (46,11) )

Total verification time: 0.54 second(s)
	Time spent in main process: 0.38 second(s)
	Time spent in child processes: 0.16 second(s)
