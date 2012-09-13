Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_548#loop$int -> [ true -> Term_552[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> UNK_548#loop$int; [
 3<=x -> UNK_549#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> [
 3<=x -> UNK_549#loop$int,
 x<=2 -> UNK_553#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_549#loop$int -> Loop_554,
UNK_553#loop$int -> [ true -> Term_556[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> [
 3<=x -> UNK_549#loop$int,
 x<=2 -> UNK_553#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_547,
 1<=x -> [
 3<=x -> Loop_554,
 x<=2 -> Term_556[ x-0]]]
!!! 
Stop Omega... 65 invocations 
0 false contexts at: ()

Total verification time: 0.096003 second(s)
	Time spent in main process: 0.072003 second(s)
	Time spent in child processes: 0.024 second(s)
