Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_536#loop$int -> Loop_539]
!!! Termination Spec:[
 x<=0 -> Term_535,
 1<=x -> UNK_536#loop$int; [
 1<=x -> UNK_537#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_535,
 1<=x -> Loop_539]
!!! 
Stop Omega... 40 invocations 
0 false contexts at: ()

Total verification time: 0.084003 second(s)
	Time spent in main process: 0.068003 second(s)
	Time spent in child processes: 0.016 second(s)
