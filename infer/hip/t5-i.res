Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 65::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 65::
                              EXISTS(Anon_566,q_567,
                              flted_7_565: x::node<Anon_566,q_567>@M[Orig] * 
                              q_567::ll<flted_7_565>@M[Orig]&Anon_566=res & 
                              n=flted_7_565+1 & 0<=(1+flted_7_565)&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd$node SUCCESS

Checking procedure tl$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_38_573,inf_next_38_574>@inf_ann_572[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 68::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_38_573,inf_next_38_574>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 68::
                      emp&inf_next_38_574=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure tl$node SUCCESS

Checking procedure hdtl$node... 
( ) :t5-i.ss:30: 9: Proving precondition in method failed


(Cause of PreCond Failure):t5-i.ss:30: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        fe_kind: MAY
        fe_name: logical bug
        fe_locs: {
                  fc_message: failed in entailing pure formula(s) in conseq
                  fc_current_lhs_flow: {FLOW,(22,23)=__norm}}
 ]

Context of Verification Failure: File "t5-i.ss",Line:27,Col:9
Last Proving Location: File "t5-i.ss",Line:30,Col:9

ERROR: at t5-i.ss_30_9 
Message: Proving precondition in method failed.
 
Procedure hdtl$node FAIL-2

Exception Failure("Proving precondition in method failed.") Occurred!

Error(s) detected when checking procedure hdtl$node

Termination checking result:

Stop Omega... 105 invocations 
0 false contexts at: ()

Total verification time: 0.82 second(s)
	Time spent in main process: 0.79 second(s)
	Time spent in child processes: 0.03 second(s)

