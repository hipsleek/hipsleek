Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure remove_min$node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null, x!=null]
!!! REL :  A(s,res,s1)
!!! POST:  res>=s & s1>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [x,A]
              EBase exists (Expl)(Impl)[s; 
                    b](ex)x::bst<s,b>@M[Orig][LHSCase]&true&
                    {FLOW,(22,23)=__norm}[]
                      EBase emp&MayLoop&{FLOW,(1,25)=__flow}[]
                              EAssume 66::ref [x]
                                EXISTS(b_34,
                                s1: x'::bst<s1,b_34>@M[Orig][LHSCase]&
                                A(s,res,s1) & b=b_34&{FLOW,(22,23)=__norm})[])
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[s; b](ex)x::bst<s,b>@M[Orig][LHSCase]&
                  true&{FLOW,(22,23)=__norm}[]
                    EBase emp&x!=null & MayLoop&{FLOW,(1,25)=__flow}[]
                            EAssume 66::ref [x]
                              EXISTS(b_34,
                              s1: x'::bst<s1,b_34>@M[Orig][LHSCase]&b=b_34 & 
                              res>=s & s1>=res&{FLOW,(22,23)=__norm})[])
!!! NEW RELS:[ (s<=res & res<=s1) --> A(s,res,s1),
 (s=s_629 & s1=s1_639 & A(s_629,res,s1_639)) --> A(s,res,s1)]
!!! NEW ASSUME:[]
Procedure remove_min$node2 SUCCESS

Termination checking result:

Stop Omega... 74 invocations 
0 false contexts at: ()

Total verification time: 0.3 second(s)
	Time spent in main process: 0.27 second(s)
	Time spent in child processes: 0.03 second(s)

