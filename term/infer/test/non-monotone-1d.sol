Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_526#loop$int -> [ x=2 -> Term_535]]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> UNK_526#loop$int,
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 x=2 -> Term_535,
 3<=x -> UNK_536#loop$int,
 x<=1 -> UNK_537#loop$int],
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_536#loop$int -> Loop_538,
UNK_527#loop$int -> Loop_539,
UNK_537#loop$int -> Loop_540]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 x=2 -> Term_535,
 3<=x -> UNK_536#loop$int,
 x<=1 -> UNK_537#loop$int],
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 x=2 -> Term_535,
 3<=x -> Loop_538,
 x<=1 -> Loop_540],
 x<=(0-1) -> Loop_539]
!!! 
Stop Omega... 70 invocations 
0 false contexts at: ()

Total verification time: 0.096004 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.032001 second(s)
