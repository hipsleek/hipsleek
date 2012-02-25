
Processing file "dll_ms.ss"
Parsing dll_ms.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append2$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[q; 
                    p](ex)x::dll<q>@M[Orig][LHSCase] * 
                    y::dll<p>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                EXISTS(q_169: x::dll<q_169>@M[Orig][LHSCase]&
                                q_169=q&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[q; p](ex)x::dll<q>@M[Orig][LHSCase] * 
                  y::dll<p>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              x::dll<q_169>@M[Orig][LHSCase]&q=q_169&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append2$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
( [(365::,0 ); (365::,0 )]) :dll_ms.ss:238: 6: bind: node  v_node_238_978'::node<val_238_979',prev_238_980',next_238_981'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):dll_ms.ss:238: 6:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(365::,0 ); (365::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    15.1 v_node_238_978'=null & v_node_238_978'=q_1611 |-  v_node_238_978'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

Procedure Call:dll_ms.ss:248: 2: 
Verification Context:(Line:231,Col:9)
Proving precondition in method delete$node~int for spec:
 ((None,[]),EBase exists (Expl)(Impl)[p_1684](ex)v_node_248_1013'::dll<p_1684>@M[Orig][LHSCase]&
                  v_node_248_1013'!=null&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 55::
                              EXISTS(p_1304: v_node_248_1013'::dll<p_1304>@M[Orig][LHSCase]&
                              p_1304=p_1684&{FLOW,(20,21)=__norm}))
Current States: [ x'::node<Anon_1673,p_1671,q_1674>@M[Orig] * q_1674::dll<self_1672>@M[Orig]&p_1671=p & self_1672=x' & x'=x & a'=a & x!=null & tmp_162'=null & a'!=1 & 673::!(v_bool_236_1014') & a'!=1 & !(v_bool_236_1014') & v_node_248_1013'=q_1674 & v_int_248_1012'+1=a'&{FLOW,(20,21)=__norm}
 es_var_measures: MayLoop] has failed 


Procedure delete$node~int result FAIL-1

Checking procedure delete2$node~int... 
Procedure delete2$node~int SUCCESS

Checking procedure delete_list$node... 
!!! REL :  A(x')
!!! POST:  x'=null
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [A]
              EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&A(x')&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_15](ex)x::dll<Anon_15>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 2::ref [x]
                              true&x'=null&{FLOW,(20,21)=__norm})
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
              EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      ECase case {
                             x=null -> ((None,[]),EBase true&MayLoop&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 4::
                                                            true&EMPT1(res)&
                                                            {FLOW,(20,21)=__norm})
                             ;
                             x!=null -> ((None,[]),EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 5::
                                                             true&EMPT2(res)&
                                                             {FLOW,(20,21)=__norm})
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_16](ex)x::dll<Anon_16>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    ECase case {
                           x=null -> ((None,[]),EBase true&MayLoop&
                                                      {FLOW,(1,23)=__flow}
                                                        EAssume 4::
                                                          true&res & x=null&
                                                          {FLOW,(20,21)=__norm})
                           ;
                           x!=null -> ((None,[]),EBase true&MayLoop&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 5::
                                                           true&!(res) & 
                                                           x!=null&
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
              EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_19](ex)x::dll<Anon_19>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              self_2071::node<Anon_2072,p_2070,q_2073>@M[Orig] * 
                              q_2073::dll<self_2071>@M[Orig]&
                              Anon_19=p_2070 & x=self_2071 & res=Anon_2072&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure front$node SUCCESS

Checking procedure get_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_33](ex)x::dll<Anon_33>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_33](ex)x::dll<Anon_33>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              self_2094::node<Anon_2095,prev_166_1116',next_165_1113'>@M[Orig]&
                              x=self_2094 & res=q_2096 & 
                              prev_166_1116'=null & next_165_1113'=null&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_next$node SUCCESS

Checking procedure get_next_next$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_43](ex)x::dll<Anon_43>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 50::
                                EXISTS(Anon_44: res::dll<Anon_44>@M[Orig][LHSCase]&
                                true&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_43](ex)x::dll<Anon_43>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 50::
                              
                              self_2126::node<Anon_2127,p_2125,q_2128>@M[Orig] * 
                              res::dll<Anon_44>@M[Orig][LHSCase]&
                              Anon_43=p_2125 & self_2126=p_2161 & x=p_2161 & 
                              res=q_2164 & Anon_44=q_2128 & 
                              self_2162=q_2128 & q_2128!=null&
                              {FLOW,(20,21)=__norm}
                              or self_2126::node<Anon_2127,p_2125,q_2128>@M[Orig] * 
                                 res::dll<Anon_44>@M[Orig][LHSCase]&
                                 Anon_43=p_2125 & x=self_2126 & 
                                 q_2128=null & res=null&{FLOW,(20,21)=__norm}
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
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 52::
                                EXISTS(p_163: x::dll<p_163>@M[Orig][LHSCase]&
                                p_163=p&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 52::
                              x::dll<p_163>@M[Orig][LHSCase]&p=p_163&
                              {FLOW,(20,21)=__norm})
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
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 100::
                                EXISTS(p_139: x::dll<p_139>@M[Orig][LHSCase]&
                                p_139=p&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 100::
                              x::dll<p_139>@M[Orig][LHSCase]&p=p_139&
                              {FLOW,(20,21)=__norm})
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
              EBase exists (Expl)(Impl)[Anon_29](ex)x::dll<Anon_29>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::ref [x]
                                EXISTS(Anon_30: x'::dll<Anon_30>@M[Orig][LHSCase]&
                                true&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_29](ex)x::dll<Anon_29>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 23::ref [x]
                              
                              tmp_171'::node<Anon_3145,p_3143,next_121_1164'>@M[Orig] * 
                              x'::dll<Anon_30>@M[Orig][LHSCase]&
                              Anon_29=p_3143 & tmp_171'=x & res=x & 
                              next_121_1164'=null & x'=null&
                              {FLOW,(20,21)=__norm}
                              or tmp_171'::node<Anon_3145,p_3143,next_127_1180'>@M[Orig] * 
                                 x'::dll<Anon_30>@M[Orig][LHSCase]&
                                 Anon_29=p_3143 & tmp_171'=x & res=x & 
                                 Anon_30=null & next_127_1180'=null & 
                                 x'!=null&{FLOW,(20,21)=__norm}
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
                    q](ex)xs::dll<p>@M[Orig][LHSCase] * 
                    ys::dll<q>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 77::ref [xs;ys]
                                EXISTS(Anon_48: ys'::dll<Anon_48>@M[Orig][LHSCase]&
                                REVERSE(xs')&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p; q](ex)xs::dll<p>@M[Orig][LHSCase] * 
                  ys::dll<q>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 77::ref [xs;ys]
                              ys'::dll<Anon_48>@M[Orig][LHSCase]&xs'=null&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (xs'=null) --> REVERSE(xs')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_34; 
                    Anon_35](ex)x::dll<Anon_34>@M[Orig][LHSCase] * 
                    y::dll<Anon_35>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::
                                EXISTS(Anon_36: x::dll<Anon_36>@M[Orig][LHSCase]&
                                true&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_34; 
                  Anon_35](ex)x::dll<Anon_34>@M[Orig][LHSCase] * 
                  y::dll<Anon_35>@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 39::
                              x::dll<Anon_36>@M[Orig][LHSCase]&x=self_3527 & 
                              Anon_36=Anon_34 & y!=null&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_40](ex)x::dll<Anon_40>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 48::
                                EXISTS(flted_199_165,Anon_41,
                                Anon_42: x::node<Anon_41,Anon_42,flted_199_165>@M[Orig]&
                                flted_199_165=null&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_40](ex)x::dll<Anon_40>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 48::
                              x::node<Anon_41,Anon_42,flted_199_165>@M[Orig]&
                              x=self_3624 & Anon_42=Anon_40 & 
                              flted_199_165=null&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[Anon_37](ex)x::dll<Anon_37>@M[Orig][LHSCase]&
                    true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 44::
                                EXISTS(flted_187_167,Anon_38,
                                Anon_39: x::node<Anon_38,Anon_39,flted_187_167>@M[Orig]&
                                flted_187_167=null&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[Anon_37](ex)x::dll<Anon_37>@M[Orig][LHSCase]&
                  true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 44::
                              x::node<Anon_38,Anon_39,flted_187_167>@M[Orig]&
                              x=self_3653 & Anon_39=Anon_37 & 
                              flted_187_167=null&{FLOW,(20,21)=__norm})
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
              EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]&0<a&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 85::ref [x]
                                EXISTS(p_146,
                                Anon_49: x'::dll<p_146>@M[Orig][LHSCase] * 
                                res::dll<Anon_49>@M[Orig][LHSCase]&p_146=p&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[p](ex)x::dll<p>@M[Orig][LHSCase]&1<=a&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 85::ref [x]
                              x'::dll<p_146>@M[Orig][LHSCase] * 
                              res::dll<Anon_49>@M[Orig][LHSCase]&x=x' & 
                              p=p_146 & 2<=a&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 1217 invocations 
7 false contexts at: ( (469,6)  (192,13)  (192,4)  (43,17)  (43,24)  (44,7)  (44,14) )

Total verification time: 2.28 second(s)
	Time spent in main process: 2. second(s)
	Time spent in child processes: 0.28 second(s)
