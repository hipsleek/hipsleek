

int foo(int x)
/*@
  requires x=1
  ensures res=1;
*/
{
  switch (x) {
  case 1: case 2: x = x + 1; x = x + 2; if (x == 1) {x = x + 1;} else {x = x + 3; x = x + 5;}; x = x + 3; break;
  case 3: x = x + 5; break;
  default: x = x + 2;
  }
  return 1;
}
