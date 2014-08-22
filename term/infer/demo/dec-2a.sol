Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_525#loop$int~int -> [ 0<=y -> Loop_532, y<=(0-1) -> Term_533[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_524,
 1<=x -> UNK_525#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_524,
 1<=x -> [
 0<=y -> Loop_532,
 y<=(0-1) -> UNK_534#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_534#loop$int~int -> [ true -> Term_537[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_524,
 1<=x -> [
 0<=y -> Loop_532,
 y<=(0-1) -> UNK_534#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_524,
 1<=x -> [
 0<=y -> Loop_532,
 y<=(0-1) -> Term_537[ x-0]]]
!!! 
Stop Omega... 58 invocations 
0 false contexts at: ()

Total verification time: 0.092004 second(s)
	Time spent in main process: 0.068004 second(s)
	Time spent in child processes: 0.024 second(s)
