Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_538#loop$int~int~int -> [ m<=1 -> Loop_554, 2<=m -> Term_555[ 0-(y-x)]],
UNK_539#loop$int~int~int -> [ 1<=m -> Loop_556, m<=0 -> Term_557[ y-x]]]
!!! Termination Spec:[
 y=x -> Term_537,
 y<x -> UNK_538#loop$int~int~int,
 x<y -> UNK_539#loop$int~int~int]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_537,
 y<x -> [
 m<=1 -> Loop_554,
 2<=m -> UNK_558#loop$int~int~int],
 x<y -> [
 1<=m -> Loop_556,
 m<=0 -> UNK_559#loop$int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_554 -> Loop_560,
Loop_556 -> Loop_561,
UNK_558#loop$int~int~int -> [ true -> Term_568[ 0-(y-x)]],
UNK_559#loop$int~int~int -> [ true -> Term_569[ y-x]]]
!!! Termination Spec:[
 y=x -> Term_537,
 y<x -> [
 m<=1 -> Loop_554,
 2<=m -> UNK_558#loop$int~int~int],
 x<y -> [
 1<=m -> Loop_556,
 m<=0 -> UNK_559#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_537,
 y<x -> [
 m<=1 -> Loop_554,
 2<=m -> MayLoop_570],
 x<y -> [
 1<=m -> Loop_556,
 m<=0 -> MayLoop_571]]
!!! 
Stop Omega... 93 invocations 
0 false contexts at: ()

Total verification time: 0.220013 second(s)
	Time spent in main process: 0.088005 second(s)
	Time spent in child processes: 0.132008 second(s)
