/*
while(x>=0) {
  if b {
      x=x-1;
    };
  b=not(b);
}
*/

void foo(bool b,int x)
 infer [@term]
 requires true
  ensures true;
{ 
  if (x>=0) {
    if (b) x=x-1;
    b=!(b);
    foo(b,x);
  }
}
