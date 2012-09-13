Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_526#loop$int -> [ 5<=x -> Term_534]]
!!! Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> UNK_526#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> [
 5<=x -> Term_534,
 x<=4 -> UNK_535#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_535#loop$int -> Loop_536]
!!! Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> [
 5<=x -> Term_534,
 x<=4 -> UNK_535#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_525,
 1<=x -> [
 5<=x -> Term_534,
 x<=4 -> Loop_536]]
!!! 
Stop Omega... 54 invocations 
0 false contexts at: ()

Total verification time: 0.080003 second(s)
	Time spent in main process: 0.056003 second(s)
	Time spent in child processes: 0.024 second(s)
