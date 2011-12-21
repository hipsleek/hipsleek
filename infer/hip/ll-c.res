
Processing file "ll-c.ss"
Parsing ll-c.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           ECase case {
                  n1=1 -> EAssume 1::
                            true & true & {FLOW,(20,21)=__norm} ;
                  n1!=1 -> EAssume 2::
                             true & true & {FLOW,(20,21)=__norm} 
                  }
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         ECase case {
                n1=1 -> EAssume 1::
                          q_530::ll<flted_14_528>@M[Orig] * 
                          x::node<Anon_529,y>@M[Orig] & flted_14_528=0 & 
                          n1=1 & q_530=null & n1=1 & 0<=n1 &
                          {FLOW,(20,21)=__norm}
                ;
                n1!=1 -> EBase true & n1!=0 & {FLOW,(1,23)=__flow}
                                 EAssume 2::
                                   x::node<Anon_553,q_554>@M[Orig] * 
                                   q_554::ll<flted_14_552>@M[Orig] &
                                   (n1=flted_14_552+1 & q_554!=null & 
                                   1<=flted_14_552 | n1=flted_14_552+1 & 
                                   flted_14_552<=(0 - 1) & q_554!=null) & 
                                   n1!=1 & 0<=n1 & {FLOW,(20,21)=__norm}
                
                }

( [(59::,0 ); (59::,0 )]) ::0: 0: Postcondition cannot be derived from context


(Cause of PostCond Failure)::0: 0:  List of Partial Context: [PC(1, 0)]
Failed States:
[
 Label: [(59::,0 ); (59::,0 )]
 State:
        fe_kind: MAY
        fe_name: separation entailment
        fe_locs: {
                  fc_message: (failure_code=15.3)  true |-  q_530!=null (may-bug).
                  fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
 ]
Successful States:


Context of Verification Failure: File "",Line:0,Col:0
Last Proving Location: File "ll-c.ss",Line:30,Col:11

ERROR: at _0_0 
Message: Post condition cannot be derived by the system.
 
Procedure appif$node~node FAIL-2

ExceptionFailure("Post condition cannot be derived by the system.")Occurred!

Error(s) detected when checking procedure appif$node~node
Stop Omega... 74 invocations 
2 false contexts at: ( (30,11)  (27,1) )

Total verification time: 0.51 second(s)
	Time spent in main process: 0.49 second(s)
	Time spent in child processes: 0.02 second(s)
