relation R(int x,int y,int a,int b).

void loo (int x, int y)
case {
 x <= 0 -> requires Term ensures true;
 x > 0 -> case {
   x+y <= 0 -> requires Term[x] ensures true;
   //x+y = 0 -> requires Term[] ensures true;
   x+y > 0 -> requires Loop ensures false;
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
# ex27e.ss 

# why this version not decreasing. explain

(7)->(16) (MayTerm ERR: not decreasing)  Term[63; 1; x] ->  Term[63; 1; x']

x>0, x+y=0 means y is negative

It seems that (8) led to (7) where x is then decreasing..

 */
