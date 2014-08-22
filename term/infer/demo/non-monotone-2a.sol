Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_534#loop$int -> [ x=5 -> Term_543]]
!!! Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> UNK_535#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_533,
 1<=x -> [
 x=5 -> Term_543,
 6<=x -> UNK_544#loop$int,
 x<=4 -> UNK_545#loop$int],
 x<=(0-1) -> UNK_535#loop$int]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_544#loop$int -> Loop_546,
UNK_535#loop$int -> Loop_547,
UNK_545#loop$int -> Loop_548]
!!! Termination Spec:[
 x=0 -> Term_533,
 1<=x -> [
 x=5 -> Term_543,
 6<=x -> UNK_544#loop$int,
 x<=4 -> UNK_545#loop$int],
 x<=(0-1) -> UNK_535#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_533,
 1<=x -> [
 x=5 -> Term_543,
 6<=x -> Loop_546,
 x<=4 -> Loop_548],
 x<=(0-1) -> Loop_547]
!!! 
Stop Omega... 72 invocations 
0 false contexts at: ()

Total verification time: 0.096004 second(s)
	Time spent in main process: 0.064003 second(s)
	Time spent in child processes: 0.032001 second(s)
