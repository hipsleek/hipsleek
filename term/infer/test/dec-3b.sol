Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_538#loop$int~int -> Loop_539,
UNK_537#loop$int~int -> [ exists(alpha:0=y+x+(2*alpha)) -> Term_544[ 0-(y-x)]]]
!!! Termination Spec:[
 y=x -> Term_536,
 y<x -> UNK_537#loop$int~int,
 x<y -> UNK_538#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_536,
 y<x -> [
 exists(alpha:0=y+x+(2*alpha)) -> UNK_547#loop$int~int,
 exists(alpha:2*alpha=1+y+x) -> UNK_546#loop$int~int],
 x<y -> Loop_539]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_539 -> Loop_548,
UNK_546#loop$int~int -> Loop_549,
UNK_547#loop$int~int -> [ true -> Term_558[ 0-(y-x)]]]
!!! Termination Spec:[
 y=x -> Term_536,
 y<x -> [
 exists(alpha:0=y+x+(2*alpha)) -> UNK_547#loop$int~int,
 exists(alpha:2*alpha=1+y+x) -> UNK_546#loop$int~int],
 x<y -> Loop_539]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_536,
 y<x -> [
 exists(alpha:0=y+x+(2*alpha)) -> Term_558[ 0-(y-x)],
 exists(alpha:2*alpha=1+y+x) -> Loop_549],
 x<y -> Loop_539]
!!! 
Stop Omega... 72 invocations 
0 false contexts at: ()

Total verification time: 0.144007 second(s)
	Time spent in main process: 0.072004 second(s)
	Time spent in child processes: 0.072003 second(s)
