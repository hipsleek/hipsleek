Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure hd0$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_next_20_558::node<inf_val_21_564,inf_next_21_565>@inf_ann_563[Orig], x::node<inf_val_20_557,inf_next_20_558>@inf_ann_556[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 67::ref [x]
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase inf_next_20_558::node<inf_val_21_564,inf_next_21_565>@L[Orig] * 
                  x::node<inf_val_20_557,inf_next_20_558>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}[]
                    EAssume 67::ref [x]
                      true&x'=inf_next_20_558 & inf_val_21_564=res&
                      {FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd0$node SUCCESS

Checking procedure hd1$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ x::node<inf_val_33_571,inf_next_33_572>@inf_ann_570[Orig]]
!!! Inferred Pure :[]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase true&true&{FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 69::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase x::node<inf_val_33_571,inf_next_33_572>@L[Orig]&MayLoop&
                  {FLOW,(1,23)=__flow}[]
                    EAssume 69::
                      true&inf_val_33_571=res&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd1$node SUCCESS

Checking procedure hd2$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 70::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&x!=null & MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 70::
                              EXISTS(x',Anon_589,q_590,
                              flted_8_588: x'::node<Anon_589,q_590>@M[Orig] * 
                              q_590::ll<flted_8_588>@M[Orig]&x'=x & 
                              Anon_589=res & n=flted_8_588+1 & 0<=(1+
                              flted_8_588)&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd2$node SUCCESS

Checking procedure hd3$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0]
!!! OLD SPECS: ((None,[]),EInfer [n]
              EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 71::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&(1<=n | n<=(0-1)) & MayLoop&
                          {FLOW,(1,23)=__flow}[]
                            EAssume 71::
                              EXISTS(x',Anon_607,q_608,
                              flted_8_606: x'::node<Anon_607,q_608>@M[Orig] * 
                              q_608::ll<flted_8_606>@M[Orig]&x'=x & 
                              Anon_607=res & n=flted_8_606+1 & 0<=(1+
                              flted_8_606)&{FLOW,(20,21)=__norm})[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd3$node SUCCESS

Checking procedure hd4$node... 
( ) :t2-i.ss:71: 9: bind: node  x'::node<val_71_515',next_71_516'>@L[Orig] cannot be derived from context


(Cause of Bind Failure):t2-i.ss:71: 9:  List of Failesc Context: [FEC(1, 0, 0 )]
Failed States:
[
 Label: 
 State:
        
         fe_kind: MUST
         fe_name: logical bug
         fe_locs: {
                   fc_message: 15.1 x'=null & x'=x |-  x'!=null (must-bug).
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
                    {FLOW,(20,21)=__norm}[]
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                              EAssume 72::
                                true&true&{FLOW,(20,21)=__norm}[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::ll<n>@M[Orig][LHSCase]&true&
                  {FLOW,(20,21)=__norm}[]
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}[]
                            EAssume 72::
                              true&0<=n&{FLOW,(20,21)=__norm}[])
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure hd4$node result FAIL-1

Termination checking result:

Stop Omega... 77 invocations 
0 false contexts at: ()

Total verification time: 0.22 second(s)
	Time spent in main process: 0.2 second(s)
	Time spent in child processes: 0.02 second(s)
