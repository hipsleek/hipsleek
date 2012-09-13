Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_537#loop$int -> [ true -> Term_541[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_536,
 1<=x -> UNK_537#loop$int; [
 1<=x -> UNK_538#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_536,
 1<=x -> [
 1<=x -> UNK_538#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_538#loop$int -> Loop_542]
!!! Termination Spec:[
 x<=0 -> Term_536,
 1<=x -> [
 1<=x -> UNK_538#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_536,
 1<=x -> [
 1<=x -> Loop_542]]
!!! 
Stop Omega... 48 invocations 
0 false contexts at: ()

Total verification time: 0.080003 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.016 second(s)
