
relation R(int x,int y).

void loo (int x, int y)
 infer [R]
 case {
  x <= 0 -> requires R(x,y) & Term ensures true;
  x > 0 -> case {
   x+y < 0 -> requires R(x,y) & Term[x] ensures true;
   x+y >= 0 -> requires R(x,y) & Loop ensures false;
  }
 }
{
  if (x>0) {
    x = x+x+y;
    y=y+1;
    loo(x,y);
  };
}

/*
# ex27a.ss 

# this seem to verify nicely..

void loo (int x, int y)
 case {
  x <= 0 -> requires Term ensures true;
  x > 0 -> case {
   x+y < 0 -> requires Term[x] ensures true;
   x+y >= 0 -> requires Loop ensures false;
  }
 }
{
  if (x>0) {
    x = x+x+y;
    y=y+1;
    loo(x,y);
  };
}


 */
