Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_542#loop$int~int~int -> [ 0<=y & 0<=z -> UNK_550#loop$int~int~int]]
!!! Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> UNK_542#loop$int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> UNK_550#loop$int~int~int,
 y<=(0-1) -> UNK_551#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_552#loop$int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_550#loop$int~int~int -> Loop_553,
UNK_551#loop$int~int~int -> [ true -> Term_557[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> UNK_550#loop$int~int~int,
 y<=(0-1) -> UNK_551#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_552#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> Loop_553,
 y<=(0-1) -> UNK_558#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_552#loop$int~int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
Loop_553 -> Loop_559,
UNK_558#loop$int~int~int -> [ true -> Term_563[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> Loop_553,
 y<=(0-1) -> UNK_558#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_552#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> Loop_553,
 y<=(0-1) -> MayLoop_564,
 z<=(0-1) & 0<=y -> UNK_552#loop$int~int~int]]
!!! 

!!! ROUND 4
!!! SUBST:[
Loop_553 -> Loop_565,
MayLoop_564 -> MayLoop_566,
UNK_552#loop$int~int~int -> MayLoop_567]
!!! Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> Loop_553,
 y<=(0-1) -> MayLoop_564,
 z<=(0-1) & 0<=y -> UNK_552#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_541,
 1<=x -> [
 0<=y & 0<=z -> Loop_553,
 y<=(0-1) -> MayLoop_564,
 z<=(0-1) & 0<=y -> MayLoop_567]]
!!! 
Stop Omega... 95 invocations 
0 false contexts at: ()

Total verification time: 0.164009 second(s)
	Time spent in main process: 0.092005 second(s)
	Time spent in child processes: 0.072004 second(s)
