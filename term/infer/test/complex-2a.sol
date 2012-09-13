Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_537#loop$int~int -> [ true -> Term_543[ 5-x]],
UNK_538#loop$int~int -> [ true -> Term_544[ 5-x]]]
!!! Termination Spec:[
 5<=x -> Term_535,
 x=y & y<=4 -> UNK_536#loop$int~int,
 y<x & x<=4 -> UNK_537#loop$int~int,
 x<=4 & x<=(y-1) -> UNK_538#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 5<=x -> Term_535,
 x=y & y<=4 -> UNK_536#loop$int~int,
 y<x & x<=4 -> Term_543[ 5-x],
 x<=4 & x<=(y-1) -> UNK_545#loop$int~int]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_536#loop$int~int -> [ 1<=x -> Loop_558, x<=0 -> Term_559[ (y-x)+1]],
UNK_545#loop$int~int -> [ true -> Term_560[ 5-x]]]
!!! Termination Spec:[
 5<=x -> Term_535,
 x=y & y<=4 -> UNK_536#loop$int~int,
 y<x & x<=4 -> Term_543[ 5-x],
 x<=4 & x<=(y-1) -> UNK_545#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 5<=x -> Term_535,
 x=y & y<=4 -> [
 1<=x -> Loop_558,
 x<=0 -> UNK_561#loop$int~int],
 y<x & x<=4 -> Term_543[ 5-x],
 x<=4 & x<=(y-1) -> UNK_562#loop$int~int]
!!! 

!!! ROUND 3
!!! SUBST:[
Loop_558 -> Loop_563,
UNK_561#loop$int~int -> [ true -> Term_568],
UNK_562#loop$int~int -> [ true -> Term_569[ 5-x]]]
!!! Termination Spec:[
 5<=x -> Term_535,
 x=y & y<=4 -> [
 1<=x -> Loop_558,
 x<=0 -> UNK_561#loop$int~int],
 y<x & x<=4 -> Term_543[ 5-x],
 x<=4 & x<=(y-1) -> UNK_562#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 5<=x -> Term_535,
 x=y & y<=4 -> [
 1<=x -> Loop_558,
 x<=0 -> Term_568],
 y<x & x<=4 -> Term_543[ 5-x],
 x<=4 & x<=(y-1) -> MayLoop_570]
!!! 
Stop Omega... 96 invocations 
0 false contexts at: ()

Total verification time: 0.108005 second(s)
	Time spent in main process: 0.068003 second(s)
	Time spent in child processes: 0.040002 second(s)
