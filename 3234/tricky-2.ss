void tricky(ref int x, ref int y)
 case {
   x<=y -> requires Term
           ensures x'=x & y'=y;
   x>y & x<=1 -> requires Term[1,-x+1]
                 ensures x'<=y';
   x>y & x>1 ->  requires Term[0,x-y]
                 ensures x'<=y';
  }
{
  if (x>y) {
    y=x+y;
    x=x+1;
    tricky(x,y);
  }
}

