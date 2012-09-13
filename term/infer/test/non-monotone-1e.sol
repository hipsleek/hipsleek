Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_535#loop$int -> [ (0-1)<=x -> Term_537[ 0-(x-0)]]]
!!! Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> UNK_535#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> [
 (0-1)<=x -> UNK_539#loop$int,
 x<=(0-2) -> UNK_538#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_538#loop$int -> Loop_540,
UNK_534#loop$int -> Loop_541,
UNK_539#loop$int -> [ true -> Term_543]]
!!! Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> [
 (0-1)<=x -> UNK_539#loop$int,
 x<=(0-2) -> UNK_538#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_533,
 1<=x -> Loop_541,
 x<=(0-1) -> [
 (0-1)<=x -> Term_543,
 x<=(0-2) -> Loop_540]]
!!! 
Stop Omega... 65 invocations 
0 false contexts at: ()

Total verification time: 0.100005 second(s)
	Time spent in main process: 0.060003 second(s)
	Time spent in child processes: 0.040002 second(s)
