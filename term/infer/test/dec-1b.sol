Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_527#loop$int -> Loop_528,
UNK_526#loop$int -> [ true -> Term_530[ x-0]]]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> UNK_526#loop$int,
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> Term_530[ x-0],
 x<=(0-1) -> Loop_528]
!!! 
Stop Omega... 47 invocations 
0 false contexts at: ()

Total verification time: 0.104005 second(s)
	Time spent in main process: 0.060003 second(s)
	Time spent in child processes: 0.044002 second(s)
