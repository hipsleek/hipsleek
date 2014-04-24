//see ../hip/global3.ss

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

void increase_n(int k)
/*@
  requires true
  ensures n'=k+n;
*/
// writes n
{
  n = n+k;
}
