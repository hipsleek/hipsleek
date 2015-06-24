relation R(int x,int y,int a,int b).

void loo (int x, int y)
infer [@term]
case {
 x <= 0 -> ensures true;
 x > 0 -> case {
   x+y < 0 -> ensures true;
   x+y = 0 -> ensures true;
   x+y > 0 -> ensures true;
 }
}
{
  if (x>0) {
   x = x+x+y; 
    y = y - 1;
    loo(x,y);
  };
}

/*
# ex27d2.ss 


 */
