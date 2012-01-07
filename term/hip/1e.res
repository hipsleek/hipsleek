
Processing file "valid-1e.ss"
Parsing valid-1e.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure foo$int... OLD SPECS:  EInfer [p1,p2]
   ECase case {
          x<0 -> EBase true & Loop & {FLOW,(20,21)=__norm}
                         EAssume 1::
                           false & false & {FLOW,(20,21)=__norm}
          ;
          x=0 -> EBase true & Term[0,p1,x+1] & {FLOW,(20,21)=__norm}
                         EAssume 2::
                           true & res=0 & {FLOW,(20,21)=__norm}
          ;
          0<x -> EBase true & Term[0,p2,x] & {FLOW,(20,21)=__norm}
                         EAssume 3::
                           true & res=x+x & {FLOW,(20,21)=__norm}
          
          }
NEW SPECS:  ECase case {
        x<0 -> EBase true & Loop & {FLOW,(20,21)=__norm}
                       EAssume 1::
                         false & false & {FLOW,(20,21)=__norm}
        ;
        x=0 -> EBase true & Term[0,p1,x+1] & {FLOW,(20,21)=__norm}
                       EAssume 2::
                         true & x=0 & res=0 & x=0 & {FLOW,(20,21)=__norm}
        ;
        0<x -> EBase true & Term[0,p2,x] & {FLOW,(20,21)=__norm}
                       EAssume 3::
                         
                         true & res=2 & x=1 & 0<x & {FLOW,(20,21)=__norm}
                         or true & res=2*x & 2<=x & 0<x &
                            {FLOW,(20,21)=__norm}
                         
        
        }
NEW RELS: []

Procedure foo$int SUCCESS

Termination checking result:
(9)->(15) (ERR: not bounded) 
(9)->(15) (ERR: not decreasing) Term[0; p2; x]->Term[0; p2_550; v_int_15_474']
(9)->(15) (ERR: not decreasing) Term[0; p2; x]->Term[0; p1_549; v_int_15_474'+1]
(7)->(15) (ERR: not bounded) 

Stop Omega... 109 invocations 
8 false contexts at: ( (15,17)  (15,15)  (15,11)  (15,9)  (15,2)  (15,9)  (13,2)  (13,9) )

Total verification time: 0.472028 second(s)
	Time spent in main process: 0.320019 second(s)
	Time spent in child processes: 0.152009 second(s)
