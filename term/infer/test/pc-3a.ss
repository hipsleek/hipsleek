void loop (int x, int y, int z)
requires true
ensures true;
{
	if (x<=0) return;
	else loop(x+y, y+z, z);
}

/*
!!! Inferred Termination Spec:[
 x<=0 -> Term_533,
 1<=x -> [
 y<=(0-1) & z<=0 -> Term_564,
 0<=y -> [
 0<=z -> Loop_579,
 z<=(0-1) -> Term_588],
 y<=(0-1) & 1<=z -> MayLoop_590]]
!!! 
*/
