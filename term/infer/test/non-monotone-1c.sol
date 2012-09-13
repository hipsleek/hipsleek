Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_526#loop$int -> [ x<=1 -> Term_529[ x-0]]]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> UNK_526#loop$int,
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 x<=1 -> UNK_531#loop$int,
 2<=x -> UNK_530#loop$int],
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_530#loop$int -> Loop_532,
UNK_527#loop$int -> Loop_533,
UNK_531#loop$int -> [ true -> Term_535]]
!!! Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 x<=1 -> UNK_531#loop$int,
 2<=x -> UNK_530#loop$int],
 x<=(0-1) -> UNK_527#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_525,
 1<=x -> [
 x<=1 -> Term_535,
 2<=x -> Loop_532],
 x<=(0-1) -> Loop_533]
!!! 
Stop Omega... 62 invocations 
0 false contexts at: ()

Total verification time: 0.124006 second(s)
	Time spent in main process: 0.076004 second(s)
	Time spent in child processes: 0.048002 second(s)
