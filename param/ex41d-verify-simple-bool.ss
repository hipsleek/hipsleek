/*
while(x>=0) {
  if b {
      x=x-1;
    };
  b=not(b);
}
*/

void foo(bool b,int x)
 case {
  x<0 -> requires Term ensures emp;
  x>=0 -> 
  case {
    b -> requires Term[2*x] ensures emp;
    !(b) -> requires Term[2*x+1] ensures emp;
  }
 }
{ 
  if (x>=0) {
    if (b) x=x-1;
    b=!(b);
    foo(b,x);
  }
}
