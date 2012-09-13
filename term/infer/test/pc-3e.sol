Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure loop$int~int~int~int... 
Procedure loop$int~int~int~int SUCCESS

Termination checking result:

Termination Inference for loop$int~int~int~int

!!! ROUND 1
!!! SUBST:[
UNK_553#loop$int~int~int~int -> [ y<=(0-1) & z<=0 & t<=0 -> Term_562[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> UNK_553#loop$int~int~int~int]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> UNK_566#loop$int~int~int~int,
 0<=y -> UNK_563#loop$int~int~int~int,
 y<=(0-1) & 1<=z -> UNK_564#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_565#loop$int~int~int~int]]
!!! 

!!! ROUND 2
!!! SUBST:[
UNK_566#loop$int~int~int~int -> [ true -> Term_579[ x-0]],
UNK_564#loop$int~int~int~int -> [ true -> Term_580[ x-0]],
UNK_565#loop$int~int~int~int -> [ true -> Term_581[ x-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> UNK_566#loop$int~int~int~int,
 0<=y -> UNK_563#loop$int~int~int~int,
 y<=(0-1) & 1<=z -> UNK_564#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_565#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> UNK_563#loop$int~int~int~int,
 y<=(0-1) & 1<=z -> UNK_582#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_583#loop$int~int~int~int]]
!!! 

!!! ROUND 3
!!! SUBST:[
UNK_563#loop$int~int~int~int -> [ z<=(0-1) & t<=0 -> Term_612[ y-(0-1)]],
UNK_582#loop$int~int~int~int -> [ true -> Term_613[ x-0]],
UNK_582#loop$int~int~int~int -> [ t<=(0-1) -> Term_614[ z-0]],
UNK_583#loop$int~int~int~int -> [ true -> Term_615[ x-0]],
UNK_583#loop$int~int~int~int -> [ true -> Term_616[ t-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> UNK_563#loop$int~int~int~int,
 y<=(0-1) & 1<=z -> UNK_582#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_583#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> UNK_619#loop$int~int~int~int,
 0<=z -> UNK_617#loop$int~int~int~int,
 z<=(0-1) & 1<=t -> UNK_618#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_620#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_621#loop$int~int~int~int]]
!!! 

!!! ROUND 4
!!! SUBST:[
UNK_619#loop$int~int~int~int -> [ true -> Term_650[ y-(0-1)]],
UNK_618#loop$int~int~int~int -> [ true -> Term_651[ y-(0-1)]],
UNK_620#loop$int~int~int~int -> [ true -> Term_652[ x-0]],
UNK_620#loop$int~int~int~int -> [ t<=(0-1) -> Term_653[ z-0]],
UNK_621#loop$int~int~int~int -> [ true -> Term_654[ x-0]],
UNK_621#loop$int~int~int~int -> [ true -> Term_655[ t-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> UNK_619#loop$int~int~int~int,
 0<=z -> UNK_617#loop$int~int~int~int,
 z<=(0-1) & 1<=t -> UNK_618#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_620#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_621#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> UNK_617#loop$int~int~int~int,
 z<=(0-1) & 1<=t -> UNK_656#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_657#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_658#loop$int~int~int~int]]
!!! 

!!! ROUND 5
!!! SUBST:[
UNK_617#loop$int~int~int~int -> [ t<=(0-1) -> Term_699[ z-(0-1)]],
UNK_656#loop$int~int~int~int -> [ true -> Term_700[ y-(0-1)]],
UNK_656#loop$int~int~int~int -> [ true -> Term_701[ t-0]],
UNK_657#loop$int~int~int~int -> [ true -> Term_702[ x-0]],
UNK_657#loop$int~int~int~int -> [ t<=(0-1) -> Term_703[ z-0]],
UNK_657#loop$int~int~int~int -> [ true -> Term_704[ 0-y]],
UNK_658#loop$int~int~int~int -> [ true -> Term_705[ x-0]],
UNK_658#loop$int~int~int~int -> [ true -> Term_706[ t-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> UNK_617#loop$int~int~int~int,
 z<=(0-1) & 1<=t -> UNK_656#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_657#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_658#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> UNK_708#loop$int~int~int~int,
 0<=t -> UNK_707#loop$int~int~int~int],
 z<=(0-1) & 1<=t -> UNK_709#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_710#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_711#loop$int~int~int~int]]
!!! 

!!! ROUND 6
!!! SUBST:[
UNK_708#loop$int~int~int~int -> [ true -> Term_748[ z-(0-1)]],
UNK_709#loop$int~int~int~int -> [ true -> Term_749[ y-(0-1)]],
UNK_709#loop$int~int~int~int -> [ true -> Term_750[ t-0]],
UNK_710#loop$int~int~int~int -> [ true -> Term_751[ x-0]],
UNK_710#loop$int~int~int~int -> [ t<=(0-1) -> Term_752[ z-0]],
UNK_710#loop$int~int~int~int -> [ true -> Term_753[ 0-y]],
UNK_711#loop$int~int~int~int -> [ true -> Term_754[ x-0]],
UNK_711#loop$int~int~int~int -> [ true -> Term_755[ t-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> UNK_708#loop$int~int~int~int,
 0<=t -> UNK_707#loop$int~int~int~int],
 z<=(0-1) & 1<=t -> UNK_709#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_710#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_711#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> UNK_707#loop$int~int~int~int],
 z<=(0-1) & 1<=t -> UNK_756#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_757#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_758#loop$int~int~int~int]]
!!! 

!!! ROUND 7
!!! SUBST:[
UNK_707#loop$int~int~int~int -> [ true -> Term_799[ t-(0-1)]],
UNK_756#loop$int~int~int~int -> [ true -> Term_800[ y-(0-1)]],
UNK_756#loop$int~int~int~int -> [ true -> Term_801[ t-0]],
UNK_757#loop$int~int~int~int -> [ true -> Term_802[ x-0]],
UNK_757#loop$int~int~int~int -> [ t<=(0-1) -> Term_803[ z-0]],
UNK_757#loop$int~int~int~int -> [ true -> Term_804[ 0-y]],
UNK_757#loop$int~int~int~int -> [ true -> Term_805[ 0-y]],
UNK_758#loop$int~int~int~int -> [ true -> Term_806[ x-0]],
UNK_758#loop$int~int~int~int -> [ true -> Term_807[ t-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> UNK_707#loop$int~int~int~int],
 z<=(0-1) & 1<=t -> UNK_756#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_757#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_758#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> UNK_808#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_809#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_810#loop$int~int~int~int]]
!!! 

!!! ROUND 8
!!! SUBST:[
UNK_808#loop$int~int~int~int -> [ true -> Term_855[ y-(0-1)]],
UNK_808#loop$int~int~int~int -> [ true -> Term_856[ t-0]],
UNK_808#loop$int~int~int~int -> [ true -> Term_857[ 0-z]],
UNK_809#loop$int~int~int~int -> [ true -> Term_858[ x-0]],
UNK_809#loop$int~int~int~int -> [ t<=(0-1) -> Term_859[ z-0]],
UNK_809#loop$int~int~int~int -> [ true -> Term_860[ 0-y]],
UNK_809#loop$int~int~int~int -> [ true -> Term_861[ 0-y]],
UNK_809#loop$int~int~int~int -> [ true -> Term_862[ 0-y]],
UNK_810#loop$int~int~int~int -> [ true -> Term_863[ x-0]],
UNK_810#loop$int~int~int~int -> [ true -> Term_864[ t-0]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> UNK_808#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> UNK_809#loop$int~int~int~int,
 y<=(0-1) & z<=0 & 1<=t -> UNK_810#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> UNK_865#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> Term_858[ x-0],
 y<=(0-1) & z<=0 & 1<=t -> UNK_866#loop$int~int~int~int]]
!!! 

!!! ROUND 9
!!! SUBST:[
UNK_865#loop$int~int~int~int -> [ true -> Term_895[ y-(0-1)]],
UNK_865#loop$int~int~int~int -> [ true -> Term_896[ t-0]],
UNK_865#loop$int~int~int~int -> [ true -> Term_897[ 0-z]],
UNK_865#loop$int~int~int~int -> [ true -> Term_898[ y-(0-1)]],
UNK_866#loop$int~int~int~int -> [ true -> Term_899[ x-0]],
UNK_866#loop$int~int~int~int -> [ true -> Term_900[ t-0]],
UNK_866#loop$int~int~int~int -> [ true -> Term_901[ 1-z]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> UNK_865#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> Term_858[ x-0],
 y<=(0-1) & z<=0 & 1<=t -> UNK_866#loop$int~int~int~int]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> UNK_902#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> Term_858[ x-0],
 y<=(0-1) & z<=0 & 1<=t -> Term_899[ x-0]]]
!!! 

!!! ROUND 10
!!! SUBST:[
UNK_902#loop$int~int~int~int -> [ true -> Term_923[ y-(0-1)]],
UNK_902#loop$int~int~int~int -> [ true -> Term_924[ t-0]],
UNK_902#loop$int~int~int~int -> [ true -> Term_925[ 0-z]],
UNK_902#loop$int~int~int~int -> [ true -> Term_926[ y-(0-1)]],
UNK_902#loop$int~int~int~int -> [ true -> Term_927[ y-(0-1)]]]
!!! Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> UNK_902#loop$int~int~int~int],
 y<=(0-1) & 1<=z -> Term_858[ x-0],
 y<=(0-1) & z<=0 & 1<=t -> Term_899[ x-0]]]
!!! 

!!! Inferred Termination Spec:[
 x<=0 -> Term_552,
 1<=x -> [
 y<=(0-1) & z<=0 & t<=0 -> Term_579[ x-0],
 0<=y -> [
 z<=(0-1) & t<=0 -> Term_650[ y-(0-1)],
 0<=z -> [
 t<=(0-1) -> Term_748[ z-(0-1)],
 0<=t -> Term_799[ t-(0-1)]],
 z<=(0-1) & 1<=t -> Term_923[ y-(0-1)]],
 y<=(0-1) & 1<=z -> Term_858[ x-0],
 y<=(0-1) & z<=0 & 1<=t -> Term_899[ x-0]]]
!!! 
Stop Omega... 289 invocations 
0 false contexts at: ()

Total verification time: 0.676041 second(s)
	Time spent in main process: 0.264016 second(s)
	Time spent in child processes: 0.412025 second(s)
