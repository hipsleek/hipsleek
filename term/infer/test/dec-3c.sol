Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_538#loop$int~int~int -> [ m<=1 -> Loop_546, 2<=m -> Term_547[ x-y]]]
!!! Termination Spec:[
 x<=y -> Term_537,
 y<x -> UNK_538#loop$int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=y -> Term_537,
 y<x -> [
 m<=1 -> Loop_546,
 2<=m -> UNK_548#loop$int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_548#loop$int~int~int -> [ true -> Term_552[ x-y]]]
!!! Termination Spec:[
 x<=y -> Term_537,
 y<x -> [
 m<=1 -> Loop_546,
 2<=m -> UNK_548#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=y -> Term_537,
 y<x -> [
 m<=1 -> Loop_546,
 2<=m -> Term_552[ x-y]]]
!!! 
Stop Omega... 60 invocations 
0 false contexts at: ()

Total verification time: 0.100005 second(s)
	Time spent in main process: 0.072004 second(s)
	Time spent in child processes: 0.028001 second(s)
