Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_533#loop$int~int -> [ 0<=y -> Loop_540]]
!!! Termination Spec:[
 x<=0 -> Term_532,
 1<=x -> UNK_533#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_540,
 y<=(0-1) -> UNK_541#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_540 -> Loop_542,
UNK_541#loop$int~int -> [ true -> Term_545[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_540,
 y<=(0-1) -> UNK_541#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_540,
 y<=(0-1) -> MayLoop_546]]
!!! 
Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.080003 second(s)
	Time spent in main process: 0.060003 second(s)
	Time spent in child processes: 0.02 second(s)
