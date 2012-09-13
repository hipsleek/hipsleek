Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_538#loop$int~int -> Loop_539,
UNK_537#loop$int~int -> [ true -> Term_542[ 0-(y-x)]]]
!!! Termination Spec:[
 y=x -> Term_536,
 y<x -> UNK_537#loop$int~int,
 x<y -> UNK_538#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_536,
 y<x -> Term_542[ 0-(y-x)],
 x<y -> Loop_539]
!!! 
Stop Omega... 49 invocations 
0 false contexts at: ()

Total verification time: 0.096003 second(s)
	Time spent in main process: 0.056002 second(s)
	Time spent in child processes: 0.040001 second(s)
