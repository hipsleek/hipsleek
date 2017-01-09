// see ../hip/global1.ss

int k;
int n;

void increase()
/*@
  requires true
  ensures k'=k+1 & n'=n+1;
*/
// writes k,n
{
	k = k+1;
	n = n+1;
}

