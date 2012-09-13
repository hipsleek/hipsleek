Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int... 
Procedure loop$int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int

!!! ROUND 1
!!! SUBST:[
UNK_563#loop$int~int -> [ 0<=y -> Loop_574, y<=(0-1) -> Term_575[ (x-y)+1]]]
!!! Termination Spec:[
 x<y -> Term_561,
 y<x -> UNK_562#loop$int~int,
 y=x -> UNK_563#loop$int~int]
!!! 

!!! Inferred Termination Spec:[
 x<y -> Term_561,
 y<x -> UNK_562#loop$int~int,
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> UNK_576#loop$int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
Loop_574 -> Loop_577,
UNK_576#loop$int~int -> [ true -> Term_580]]
!!! Termination Spec:[
 x<y -> Term_561,
 y<x -> UNK_562#loop$int~int,
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> UNK_576#loop$int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<y -> Term_561,
 y<x -> UNK_562#loop$int~int,
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> Term_580]]
!!! 

!!! ROUND 3
!!! SUBST:[
Loop_574 -> Loop_581,
UNK_562#loop$int~int -> [ y<=(0-1) -> Term_584[ 0-(y-x)]]]
!!! Termination Spec:[
 x<y -> Term_561,
 y<x -> UNK_562#loop$int~int,
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> Term_580]]
!!! 

!!! Inferred Termination Spec:[
 x<y -> Term_561,
 y<x -> [
 y<=(0-1) -> UNK_586#loop$int~int,
 0<=y -> UNK_585#loop$int~int],
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> Term_580]]
!!! 

!!! ROUND 4
!!! SUBST:[
Loop_574 -> Loop_587,
UNK_585#loop$int~int -> Loop_588,
UNK_586#loop$int~int -> [ true -> Term_591[ 0-(y-x)]]]
!!! Termination Spec:[
 x<y -> Term_561,
 y<x -> [
 y<=(0-1) -> UNK_586#loop$int~int,
 0<=y -> UNK_585#loop$int~int],
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> Term_580]]
!!! 

!!! Inferred Termination Spec:[
 x<y -> Term_561,
 y<x -> [
 y<=(0-1) -> Term_591[ 0-(y-x)],
 0<=y -> Loop_588],
 y=x -> [
 0<=y -> Loop_574,
 y<=(0-1) -> Term_580]]
!!! 
Stop Omega... 105 invocations 
0 false contexts at: ()

Total verification time: 0.200011 second(s)
	Time spent in main process: 0.092005 second(s)
	Time spent in child processes: 0.108006 second(s)
