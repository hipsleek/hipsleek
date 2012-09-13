Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_527#loop$int -> Loop_528,
UNK_526#loop$int -> [ exists(alpha:2*alpha=x) -> Term_532[ x-0]]]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> UNK_526#loop$int,
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 exists(alpha:2*alpha=x) -> UNK_535#loop$int,
 exists(alpha:2*alpha=1+x) -> UNK_534#loop$int],
 x<=(0-1) -> Loop_528]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_528 -> Loop_536,
UNK_534#loop$int -> Loop_537,
UNK_535#loop$int -> [ true -> Term_544[ x-0]]]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 exists(alpha:2*alpha=x) -> UNK_535#loop$int,
 exists(alpha:2*alpha=1+x) -> UNK_534#loop$int],
 x<=(0-1) -> Loop_528]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 exists(alpha:2*alpha=x) -> Term_544[ x-0],
 exists(alpha:2*alpha=1+x) -> Loop_537],
 x<=(0-1) -> Loop_528]
!!! 
Stop Omega... 69 invocations 
0 false contexts at: ()

Total verification time: 0.144008 second(s)
	Time spent in main process: 0.068004 second(s)
	Time spent in child processes: 0.076004 second(s)
