Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int... 
Procedure loop$int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_534#loop$int~int~int -> [ 0<=y & 0<=z -> UNK_543#loop$int~int~int, y<=(0-1) & z<=0 -> Term_542[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> UNK_534#loop$int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 0<=y & 0<=z -> UNK_543#loop$int~int~int,
 y<=(0-1) & z<=0 -> UNK_546#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_544#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_545#loop$int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_543#loop$int~int~int -> Loop_547,
UNK_546#loop$int~int~int -> [ true -> Term_554[ x-0]],
UNK_545#loop$int~int~int -> [ true -> Term_555[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 0<=y & 0<=z -> UNK_543#loop$int~int~int,
 y<=(0-1) & z<=0 -> UNK_546#loop$int~int~int,
 z<=(0-1) & 0<=y -> UNK_544#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_545#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 0<=y & 0<=z -> Loop_547,
 y<=(0-1) & z<=0 -> Term_554[ x-0],
 z<=(0-1) & 0<=y -> UNK_544#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_556#loop$int~int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
Loop_547 -> Loop_557,
UNK_544#loop$int~int~int -> [ true -> Term_564[ y-(0-1)]],
UNK_556#loop$int~int~int -> [ true -> Term_565[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 0<=y & 0<=z -> Loop_547,
 y<=(0-1) & z<=0 -> Term_554[ x-0],
 z<=(0-1) & 0<=y -> UNK_544#loop$int~int~int,
 y<=(0-1) & 1<=z -> UNK_556#loop$int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 0<=y & 0<=z -> Loop_547,
 y<=(0-1) & z<=0 -> Term_554[ x-0],
 z<=(0-1) & 0<=y -> Term_564[ y-(0-1)],
 y<=(0-1) & 1<=z -> MayLoop_566]]
!!! 
Stop Omega... 102 invocations 
0 false contexts at: ()

Total verification time: 0.148009 second(s)
	Time spent in main process: 0.084005 second(s)
	Time spent in child processes: 0.064004 second(s)
