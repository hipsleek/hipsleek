Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_544#loop$int~int~int -> [ 0<=y & 0<=z & z<=4 -> UNK_552#loop$int~int~int]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> UNK_544#loop$int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> UNK_552#loop$int~int~int,
 y<=(0-1) -> UNK_553#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_554#loop$int~int~int,
 0<=y & 5<=z -> UNK_555#loop$int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_552#loop$int~int~int -> Loop_556,
UNK_553#loop$int~int~int -> [ true -> Term_560[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> UNK_552#loop$int~int~int,
 y<=(0-1) -> UNK_553#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_554#loop$int~int~int,
 0<=y & 5<=z -> UNK_555#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> Loop_556,
 y<=(0-1) -> UNK_561#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_554#loop$int~int~int,
 0<=y & 5<=z -> UNK_555#loop$int~int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
Loop_556 -> Loop_562,
UNK_561#loop$int~int~int -> [ true -> Term_566[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> Loop_556,
 y<=(0-1) -> UNK_561#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_554#loop$int~int~int,
 0<=y & 5<=z -> UNK_555#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> Loop_556,
 y<=(0-1) -> MayLoop_567,
 z<=(0-1) & 0<=y -> UNK_554#loop$int~int~int,
 0<=y & 5<=z -> UNK_555#loop$int~int~int]]
!!! 

!!! ROUND 4
!!! SUBST:[
MayLoop_567 -> MayLoop_568,
UNK_555#loop$int~int~int -> MayLoop_569,
UNK_554#loop$int~int~int -> MayLoop_570]
!!! Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> Loop_556,
 y<=(0-1) -> MayLoop_567,
 z<=(0-1) & 0<=y -> UNK_554#loop$int~int~int,
 0<=y & 5<=z -> UNK_555#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_543,
 1<=x -> [
 0<=y & 0<=z & z<=4 -> Loop_556,
 y<=(0-1) -> MayLoop_567,
 z<=(0-1) & 0<=y -> MayLoop_570,
 0<=y & 5<=z -> MayLoop_569]]
!!! 
Stop Omega... 112 invocations 
0 false contexts at: ()

Total verification time: 0.156009 second(s)
	Time spent in main process: 0.084005 second(s)
	Time spent in child processes: 0.072004 second(s)
