
Processing file "ll_m.ss"
Parsing ll_m.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure append$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase] * y::ll1@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 23::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase] * y::ll1@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 23::
                              x::ll1@M[Orig][LHSCase]&true&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure append$node~node SUCCESS

Checking procedure create_list$int~int... 
Procedure create_list$int~int SUCCESS

Checking procedure assign$node~int~int... 
Procedure assign$node~int~int SUCCESS

Checking procedure delete$node~int... 
( [(276::,0 ); (276::,0 )]) :ll_m.ss:209: 15: bind: node  v_node_209_748'::node<val_209_749',next_209_750'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):ll_m.ss:209: 15:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(276::,0 ); (276::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    15.1 v_node_209_748'=null & v_node_209_748'=q_1011 |-  v_node_209_748'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]&0<a&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 41::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&1<=a&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 41::
                              x::ll1@M[Orig][LHSCase]&true&
                              {FLOW,(20,21)=__norm})
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
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::ref [x]
                                true&A(x')&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
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
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
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
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
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
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              x::node<Anon_1221,q_1222>@M[Orig] * 
                              q_1222::ll1@M[Orig]&Anon_1221=res&
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
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 27::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 27::
                              x::node<Anon_1234,q_1235>@M[Orig] * 
                              q_1235::ll1@M[Orig]&q_1235=res&
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
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::
                                res::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 36::
                              
                              x::node<Anon_1248,q_1249>@M[Orig] * 
                              q_1249::node<Anon_1271,q_1272>@M[Orig] * 
                              res::ll1@M[Orig][LHSCase]&q_1272=res & 
                              q_1249!=null&{FLOW,(20,21)=__norm}
                              or x::node<Anon_1248,q_1249>@M[Orig] * 
                                 res::ll1@M[Orig][LHSCase]&q_1249=null & 
                                 res=null&{FLOW,(20,21)=__norm}
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
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 38::
                              x::ll1@M[Orig][LHSCase]&true&
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
!!! Inferred Pure :[ x!=null, x!=null, x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 72::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 72::
                              x::ll1@M[Orig][LHSCase]&true&
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
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 20::ref [x]
                                x'::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 20::ref [x]
                              tmp_98'::node<Anon_1600,next_112_846'>@M[Orig] * 
                              x'::ll1@M[Orig][LHSCase]&res=tmp_98' & 
                              x=tmp_98' & next_112_846'=null&
                              {FLOW,(20,21)=__norm})
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
              EBase xs::ll1@M[Orig][LHSCase] * ys::ll1@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 53::ref [xs;ys]
                                ys'::ll1@M[Orig][LHSCase]&REVERSE(xs')&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase xs::ll1@M[Orig][LHSCase] * ys::ll1@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 53::ref [xs;ys]
                              ys'::ll1@M[Orig][LHSCase]&xs'=null&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (xs'=null) --> REVERSE(xs')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure reverse$node~node SUCCESS

Checking procedure set_next$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase] * y::ll1@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 28::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase] * y::ll1@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              x::ll1@M[Orig][LHSCase]&true&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_next$node~node SUCCESS

Checking procedure set_null$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 34::
                                EXISTS(Anon_15,r: x::node<Anon_15,r>@M[Orig]&
                                true&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 34::
                              x::node<Anon_15,r>@M[Orig]&r=null&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure set_null$node SUCCESS

Checking procedure set_null2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::
                                EXISTS(Anon_14,r: x::node<Anon_14,r>@M[Orig]&
                                true&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 30::
                              x::node<Anon_14,r>@M[Orig]&r=null&
                              {FLOW,(20,21)=__norm})
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
              EBase x::ll1@M[Orig][LHSCase]&0<a&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::
                                x::ll1@M[Orig][LHSCase] * 
                                res::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&1<=a&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 59::
                              
                              x::ll1@M[Orig][LHSCase] * 
                              res::ll1@M[Orig][LHSCase]&a=1&
                              {FLOW,(20,21)=__norm}
                              or x::ll1@M[Orig][LHSCase] * 
                                 res::ll1@M[Orig][LHSCase]&2<=a&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 741 invocations 
6 false contexts at: ( (164,13)  (164,4)  (43,4)  (43,11)  (45,4)  (45,11) )

Total verification time: 1.03 second(s)
	Time spent in main process: 0.87 second(s)
	Time spent in child processes: 0.16 second(s)
