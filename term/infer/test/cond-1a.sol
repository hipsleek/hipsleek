Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_571#loop$int -> Loop_573,
UNK_572#loop$int -> [ true -> Term_575[ x-4]]]
!!! Termination Spec:[
 2<=x & x<=4 -> Term_570,
 x<=1 -> UNK_571#loop$int,
 5<=x -> UNK_572#loop$int]
!!! 

!!! Inferred Termination Spec:[
 2<=x & x<=4 -> Term_570,
 x<=1 -> Loop_573,
 5<=x -> Term_575[ x-4]]
!!! 
Stop Omega... 67 invocations 
0 false contexts at: ()

Total verification time: 0.084004 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.020001 second(s)
