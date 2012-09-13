Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_566#loop$int -> [ true -> Term_568[ x-0]]]
!!! Termination Spec:[
 6<=x -> Term_564,
 x<=0 -> Term_565,
 1<=x & x<=5 -> UNK_566#loop$int]
!!! 

!!! Inferred Termination Spec:[
 6<=x -> Term_564,
 x<=0 -> Term_565,
 1<=x & x<=5 -> Term_568[ x-0]]
!!! 
Stop Omega... 60 invocations 
0 false contexts at: ()

Total verification time: 0.072002 second(s)
	Time spent in main process: 0.056002 second(s)
	Time spent in child processes: 0.016 second(s)
