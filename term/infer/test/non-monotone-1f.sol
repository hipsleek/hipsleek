Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_535#loop$int -> [ x=0-2 -> Term_543]]
!!! Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> UNK_535#loop$int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> [
 x=0-2 -> Term_543,
 0<=(1+x) -> UNK_544#loop$int,
 x<=(0-3) -> UNK_545#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_545#loop$int -> Loop_546,
UNK_534#loop$int -> Loop_547,
UNK_544#loop$int -> Loop_548]
!!! Termination Spec:[
 x=0 -> Term_533,
 1<=x -> UNK_534#loop$int,
 x<=(0-1) -> [
 x=0-2 -> Term_543,
 0<=(1+x) -> UNK_544#loop$int,
 x<=(0-3) -> UNK_545#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_533,
 1<=x -> Loop_547,
 x<=(0-1) -> [
 x=0-2 -> Term_543,
 0<=(1+x) -> Loop_548,
 x<=(0-3) -> Loop_546]]
!!! 
Stop Omega... 73 invocations 
0 false contexts at: ()

Total verification time: 0.072002 second(s)
	Time spent in main process: 0.048002 second(s)
	Time spent in child processes: 0.024 second(s)
