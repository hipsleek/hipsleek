Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_552#loop$int~int -> [ 0<=(y+x) -> Loop_567]]
!!! Termination Spec:[
 x<=0 -> Term_551,
 1<=x -> UNK_552#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_551,
 1<=x -> [
 0<=(y+x) -> Loop_567,
 y<=((0-x)-1) -> UNK_568#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_567 -> Loop_569,
UNK_568#loop$int~int -> [ true -> Term_574[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_551,
 1<=x -> [
 0<=(y+x) -> Loop_567,
 y<=((0-x)-1) -> UNK_568#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_551,
 1<=x -> [
 0<=(y+x) -> Loop_567,
 y<=((0-x)-1) -> MayLoop_575]]
!!! 
Stop Omega... 63 invocations 
0 false contexts at: ()

Total verification time: 0.100004 second(s)
	Time spent in main process: 0.072003 second(s)
	Time spent in child processes: 0.028001 second(s)
