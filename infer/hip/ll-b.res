
Processing file "ll-b.ss"
Parsing ll-b.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure appif$node~node... OLD SPECS:  EInfer [n1]
   EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & n1!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           
           q_528::ll<flted_14_526>@M[Orig] * x::node<Anon_527,y>@M[Orig] &
           n1=flted_14_526+1 & q_528=null & 0<=n1 & {FLOW,(20,21)=__norm}
           or x::node<Anon_527,q_528>@M[Orig] * 
              q_528::ll<flted_14_526>@M[Orig] & n1=flted_14_526+1 & 
              q_528!=null & 0<=n1 & {FLOW,(20,21)=__norm}
           

( [(58::,0 ); (58::,0 )]) ::0: 0: Postcondition cannot be derived from context


(Cause of PostCond Failure)::0: 0:  List of Partial Context: [PC(1, 0)]
Failed States:
[
 Label: [(58::,0 ); (58::,0 )]
 State:
        
         fe_kind: MAY
         fe_name: separation entailment
         fe_locs: {
                   fc_message: (failure_code=15.3)  true |-  q_528!=null (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       FAIL_UNION 
        
         fe_kind: MAY
         fe_name: separation entailment
         fe_locs: {
                   fc_message: (failure_code=15.3)  q_528=y |-  q_528!=null (may-bug).
                   fc_current_lhs_flow: {FLOW,(1,23)=__flow}}
       
 ]
Successful States:


Context of Verification Failure: File "",Line:0,Col:0
Last Proving Location: File "ll-b.ss",Line:28,Col:11

ERROR: at _0_0 
Message: Post condition cannot be derived by the system.
 
Procedure appif$node~node FAIL-2

ExceptionFailure("Post condition cannot be derived by the system.")Occurred!

Error(s) detected when checking procedure appif$node~node
Stop Omega... 82 invocations 
0 false contexts at: ()

Total verification time: 0.56 second(s)
	Time spent in main process: 0.54 second(s)
	Time spent in child processes: 0.02 second(s)
