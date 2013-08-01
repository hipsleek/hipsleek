// see ../hip/global5.ss

int n;
int k;

void increase(int* k)
/*@
   requires k::int*<a> & a > 0
   ensures k::int*<n>;
*/
{
   *k = n;
   //dprint;
   decrease();
}

void decrease()
/*@
   requires true
   ensures k' = k-1;
*/
{
   k--;
}
