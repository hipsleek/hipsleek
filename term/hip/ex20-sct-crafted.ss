void gcd (int x, int y)
 case {
   x>0 & y>0 -> requires Term[x+y]
     ensures true;
   (x<=0 | y<=0) -> requires Term[] ensures true;
 }
{
  if (x>0 && y>0) {
    gcd(y-2,x+1);
  };
}

// above cannot be handled by normal size-change..

int randI() 
  requires Term[]
  ensures true;


void foo (int x, int y)
 case {
   x>0 & y>0 -> requires Term[x+y]
     ensures true;
   (x<=0 | y<=0) -> requires Term[] ensures true;
 }
{
  int k=randI();
  if (x>0 && y>0) {
    foo(y-2,x+1);
    foo(x-1,k);
  };
}

