int foo(int x)
  requires true
  ensures true;
{
  int y=0;
  int z=0;
  dprint;
  return 0;
}

relation LO(int x).
relation HI(int x).
  
int foo2(int x)
  requires (x=0|x=1) & HI(x)
  ensures res=(1-x) & LO(res);
 {
  int y=0;
  if(x == 0) {
    dprint; // here, there is { x=0 & HI(x) & x'=x & LO(y') & y'=0 }
    y = 1;    // and it infers ==> { LO(x) } through the equality: { x=0 & x'=x & y'=0 } from { LO(y') }
  }
  return 0;
 }
