Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_526#loop$int -> [ x<=1 -> Loop_532, 2<=x -> Term_533[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> UNK_526#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> [
 x<=1 -> Loop_532,
 2<=x -> UNK_534#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_534#loop$int -> [ true -> Term_536]]
!!! Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> [
 x<=1 -> Loop_532,
 2<=x -> UNK_534#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> [
 x<=1 -> Loop_532,
 2<=x -> Term_536]]
!!! 
Stop Omega... 56 invocations 
0 false contexts at: ()

Total verification time: 0.096005 second(s)
	Time spent in main process: 0.072004 second(s)
	Time spent in child processes: 0.024001 second(s)
