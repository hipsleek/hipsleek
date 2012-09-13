Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int~int... 
Procedure loop$int~int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_539#loop$int~int~int~int -> [ m<=n -> Loop_548, n<m -> Term_549[ x-y]]]
!!! Termination Spec:[
 x<=y -> Term_538,
 y<x -> UNK_539#loop$int~int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=y -> Term_538,
 y<x -> [
 m<=n -> Loop_548,
 n<m -> UNK_550#loop$int~int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_550#loop$int~int~int~int -> [ true -> Term_555[ x-y]]]
!!! Termination Spec:[
 x<=y -> Term_538,
 y<x -> [
 m<=n -> Loop_548,
 n<m -> UNK_550#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=y -> Term_538,
 y<x -> [
 m<=n -> Loop_548,
 n<m -> Term_555[ x-y]]]
!!! 
Stop Omega... 60 invocations 
0 false contexts at: ()

Total verification time: 0.116006 second(s)
	Time spent in main process: 0.076004 second(s)
	Time spent in child processes: 0.040002 second(s)
