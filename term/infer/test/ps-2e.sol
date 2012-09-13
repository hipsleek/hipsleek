Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int... 
Procedure loop$int SUCCESS

Termination checking result:

Termination Inference for loop$int

!!! ROUND 1
!!! SUBST:[
UNK_583#loop$int -> Loop_590,
UNK_584#loop$int -> [ true -> Term_592[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_582,
 3<=x -> UNK_583#loop$int; [
 3<=x & x<=4 -> UNK_585#loop$int,
 5<=x -> UNK_587#loop$int],
 1<=x & x<=2 -> UNK_584#loop$int; [
 1<=x & x<=2 -> UNK_586#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_582,
 3<=x -> Loop_590,
 1<=x & x<=2 -> [
 1<=x & x<=2 -> UNK_586#loop$int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_586#loop$int -> [ true -> Term_594]]
!!! Termination Spec:[
 x<=0 -> Term_582,
 3<=x -> Loop_590,
 1<=x & x<=2 -> [
 1<=x & x<=2 -> UNK_586#loop$int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_582,
 3<=x -> Loop_590,
 1<=x & x<=2 -> [
 1<=x & x<=2 -> Term_594]]
!!! 
Stop Omega... 91 invocations 
0 false contexts at: ()

Total verification time: 0.120005 second(s)
	Time spent in main process: 0.080004 second(s)
	Time spent in child processes: 0.040001 second(s)
