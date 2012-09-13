Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_535#loop$int~int -> [ x<=(0-y) -> Term_544]]
!!! Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> UNK_535#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 x<=(0-y) -> Term_544,
 1<=(x+y) -> UNK_545#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_545#loop$int~int -> Loop_546]
!!! Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 x<=(0-y) -> Term_544,
 1<=(x+y) -> UNK_545#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_534,
 1<=x -> [
 x<=(0-y) -> Term_544,
 1<=(x+y) -> Loop_546]]
!!! 
Stop Omega... 57 invocations 
0 false contexts at: ()

Total verification time: 0.092005 second(s)
	Time spent in main process: 0.068004 second(s)
	Time spent in child processes: 0.024001 second(s)
