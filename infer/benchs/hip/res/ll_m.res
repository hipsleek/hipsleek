
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
                              EAssume 24::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase] * y::ll1@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 24::
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
( [(277::,0 ); (277::,0 )]) :ll_m.ss:209: 13: bind: node  v_node_209_752'::node<val_209_753',next_209_754'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):ll_m.ss:209: 13:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: [(277::,0 ); (277::,0 )]
 State:
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 
                    15.1 v_node_209_752'=null & v_node_209_752'=q_1022 |-  v_node_209_752'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase x::ll1@M[Orig][LHSCase]&0<a&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 42::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&1<=a&{FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 42::
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
                              x::node<Anon_1232,q_1233>@M[Orig] * 
                              q_1233::ll1@M[Orig]&res=Anon_1232&
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
                              EAssume 28::
                                true&true&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 28::
                              x::node<Anon_1245,q_1246>@M[Orig] * 
                              q_1246::ll1@M[Orig]&res=q_1246&
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
                              EAssume 37::
                                res::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::
                              
                              x::node<Anon_1259,q_1260>@M[Orig] * 
                              q_1260::node<Anon_1282,q_1283>@M[Orig] * 
                              res::ll1@M[Orig][LHSCase]&res=q_1283 & 
                              q_1260!=null&{FLOW,(20,21)=__norm}
                              or x::node<Anon_1259,q_1260>@M[Orig] * 
                                 res::ll1@M[Orig][LHSCase]&q_1260=null & 
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
                              EAssume 39::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 39::
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
                              EAssume 73::
                                x::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 73::
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
                              EAssume 21::ref [x]
                                x'::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 21::ref [x]
                              tmp_102'::node<Anon_1611,next_113_852'>@M[Orig] * 
                              x'::ll1@M[Orig][LHSCase]&tmp_102'=x & res=x & 
                              next_113_852'=null&{FLOW,(20,21)=__norm})
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
                              EAssume 54::ref [xs;ys]
                                ys'::ll1@M[Orig][LHSCase]&REVERSE(xs')&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase xs::ll1@M[Orig][LHSCase] * ys::ll1@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 54::ref [xs;ys]
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
                              EAssume 29::ref [x]
                                x'::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase] * y::ll1@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [x]
                              x'::ll1@M[Orig][LHSCase]&x=x'&
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
                              EAssume 35::ref [x]
                                EXISTS(flted_172_98,
                                Anon_15: x'::node<Anon_15,flted_172_98>@M[Orig]&
                                flted_172_98=null&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 35::ref [x]
                              x'::node<Anon_15,flted_172_98>@M[Orig]&x=x' & 
                              flted_172_98=null&{FLOW,(20,21)=__norm})
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
                              EAssume 31::ref [x]
                                EXISTS(flted_160_100,
                                Anon_14: x'::node<Anon_14,flted_160_100>@M[Orig]&
                                flted_160_100=null&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&true&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [x]
                              x'::node<Anon_14,flted_160_100>@M[Orig]&x=x' & 
                              flted_160_100=null&{FLOW,(20,21)=__norm})
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
                              EAssume 60::ref [x]
                                x'::ll1@M[Orig][LHSCase] * 
                                res::ll1@M[Orig][LHSCase]&true&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase x::ll1@M[Orig][LHSCase]&1<=a&{FLOW,(20,21)=__norm}
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 60::ref [x]
                              x'::ll1@M[Orig][LHSCase] * 
                              res::ll1@M[Orig][LHSCase]&x=x' & 2<=a&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure split1$node~int SUCCESS

Checking procedure swap$node~node... 
Procedure swap$node~node SUCCESS

Termination checking result:

Stop Omega... 837 invocations 
6 false contexts at: ( (165,13)  (165,4)  (42,17)  (42,24)  (43,7)  (43,14) )

Total verification time: 1.06 second(s)
	Time spent in main process: 0.88 second(s)
	Time spent in child processes: 0.18 second(s)
