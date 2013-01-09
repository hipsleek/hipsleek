Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd0$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_next_20_574::node<inf_val_21_580,inf_next_21_581>@inf_ann_579[Orig], x::node<inf_val_20_573,inf_next_20_574>@inf_ann_572[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 67::ref [x]
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_next_20_574::node<inf_val_21_580,inf_next_21_581>@L[Orig] * 
                  x::node<inf_val_20_573,inf_next_20_574>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 67::ref [x]
                      emp&inf_next_20_574=x' & inf_val_21_580=res&
                      {FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd0$node SUCCESS

Checking procedure hd1$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_33_587,inf_next_33_588>@inf_ann_586[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase emp&true&{FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 69::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_33_587,inf_next_33_588>@L[Orig]&MayLoop&
                  {FLOW,(1,25)=__flow}[]
                    EAssume 69::
                      emp&inf_val_33_587=res&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd1$node SUCCESS

Checking procedure hd2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 70::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 70::
                              EXISTS(Anon_605,q_606,
                              flted_8_604: x::node<Anon_605,q_606>@M[Orig] * 
                              q_606::ll<flted_8_604>@M[Orig]&Anon_605=res & 
                              n=flted_8_604+1 & 0<=(1+flted_8_604)&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd2$node SUCCESS

Checking procedure hd3$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 71::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&(1<=n | n<=(0-1)) & MayLoop&
                          {FLOW,(1,25)=__flow}[]
                            EAssume 71::
                              EXISTS(Anon_623,q_624,
                              flted_8_622: x::node<Anon_623,q_624>@M[Orig] * 
                              q_624::ll<flted_8_622>@M[Orig]&Anon_623=res & 
                              n=flted_8_622+1 & 0<=(1+flted_8_622)&
                              {FLOW,(22,23)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd3$node SUCCESS

Checking procedure hd4$node... 
( ) :t2-i.ss:71: 9: bind: node  x'::node<val_71_531',next_71_532'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):t2-i.ss:71: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 15.1 x'=null & x=x' |-  x'!=null (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: MUST
         fe_name: separation entailment
         fe_locs: {
                   fc_message: 15.5 no match for rhs data node: xPRMD (must-bug).
                   fc_current_lhs_flow: {FLOW,(1,5)=__Error}}
       FAIL_OR 
        
         fe_kind: Valid
         fe_name: 
         fe_locs: Failure_Valid
       
 ]

!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 72::
                                emp&true&{FLOW,(22,23)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(22,23)=__norm}[]
                    EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 72::
                              emp&0<=n&{FLOW,(22,23)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
Procedure hd4$node result FAIL-1

Termination checking result:

Stop Omega... 80 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.26 second(s)
	Time spent in child processes: 0.04 second(s)

