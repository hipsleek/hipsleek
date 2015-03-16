void tricky(ref int x, ref int y)
 case {
   x<=y -> requires Term
           ensures x'=x & y'=y;
   x>y ->  ensures x'<=y';
  }
{
  if (x>y) {
    y=x+y;
    x=x+1;
    tricky(x,y);
  }
}

