Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_533#loop$int~int -> [ 0<=y -> Loop_547],
UNK_534#loop$int~int -> [ 1<=y -> Term_548[ 0-(x-0)]]]
!!! Termination Spec:[
 x=0 -> Term_532,
 1<=x -> UNK_533#loop$int~int,
 x<=(0-1) -> UNK_534#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_547,
 y<=(0-1) -> UNK_549#loop$int~int],
 x<=(0-1) -> [
 1<=y -> UNK_551#loop$int~int,
 y<=0 -> UNK_550#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_547 -> Loop_552,
UNK_549#loop$int~int -> [ true -> Term_557[ x-0]],
UNK_551#loop$int~int -> [ true -> Term_558[ 0-(x-0)]]]
!!! Termination Spec:[
 x=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_547,
 y<=(0-1) -> UNK_549#loop$int~int],
 x<=(0-1) -> [
 1<=y -> UNK_551#loop$int~int,
 y<=0 -> UNK_550#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_547,
 y<=(0-1) -> MayLoop_559],
 x<=(0-1) -> [
 1<=y -> MayLoop_560,
 y<=0 -> UNK_550#loop$int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
MayLoop_560 -> MayLoop_561,
UNK_550#loop$int~int -> MayLoop_562]
!!! Termination Spec:[
 x=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_547,
 y<=(0-1) -> MayLoop_559],
 x<=(0-1) -> [
 1<=y -> MayLoop_560,
 y<=0 -> UNK_550#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x=0 -> Term_532,
 1<=x -> [
 0<=y -> Loop_547,
 y<=(0-1) -> MayLoop_559],
 x<=(0-1) -> [
 1<=y -> MayLoop_560,
 y<=0 -> MayLoop_562]]
!!! 
Stop Omega... 96 invocations 
0 false contexts at: ()

Total verification time: 0.16801 second(s)
	Time spent in main process: 0.064004 second(s)
	Time spent in child processes: 0.104006 second(s)
