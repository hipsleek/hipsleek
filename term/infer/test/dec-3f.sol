Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int~int... 
Procedure loop$int~int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_539#loop$int~int~int~int -> [ m<=n -> Loop_557, n<m -> Term_558[ 0-(y-x)]],
UNK_540#loop$int~int~int~int -> [ n<=m -> Loop_559, m<n -> Term_560[ y-x]]]
!!! Termination Spec:[
 y=x -> Term_538,
 y<x -> UNK_539#loop$int~int~int~int,
 x<y -> UNK_540#loop$int~int~int~int]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_538,
 y<x -> [
 m<=n -> Loop_557,
 n<m -> UNK_561#loop$int~int~int~int],
 x<y -> [
 n<=m -> Loop_559,
 m<n -> UNK_562#loop$int~int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_557 -> Loop_563,
Loop_559 -> Loop_564,
UNK_561#loop$int~int~int~int -> [ true -> Term_573[ 0-(y-x)]],
UNK_562#loop$int~int~int~int -> [ true -> Term_574[ y-x]]]
!!! Termination Spec:[
 y=x -> Term_538,
 y<x -> [
 m<=n -> Loop_557,
 n<m -> UNK_561#loop$int~int~int~int],
 x<y -> [
 n<=m -> Loop_559,
 m<n -> UNK_562#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 y=x -> Term_538,
 y<x -> [
 m<=n -> Loop_557,
 n<m -> MayLoop_575],
 x<y -> [
 n<=m -> Loop_559,
 m<n -> MayLoop_576]]
!!! 
Stop Omega... 92 invocations 
0 false contexts at: ()

Total verification time: 0.208011 second(s)
	Time spent in main process: 0.084004 second(s)
	Time spent in child processes: 0.124007 second(s)
