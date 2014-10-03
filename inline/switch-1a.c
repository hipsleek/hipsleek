

int foo(int x)
/*@
  requires x=1
  ensures res=1;
*/
{
  switch (x){
  case 1: return 1;
  case 2: return 0;
  }
}
