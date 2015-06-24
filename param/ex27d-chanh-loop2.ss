relation R(int x,int y,int a,int b).

void loo (int x, int y)
case {
 x <= 0 -> requires Term ensures true;
 x > 0 -> case {
   x+y < 0 -> requires Term[x] ensures true;
   x+y = 0 -> requires Term[] ensures true;
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
# ex27c.ss 

case {
 x <= 0 -> requires Term ensures true;
 x > 0 -> case {
   x+y <= 0 -> requires Term[x+y] ensures true;
   x+y > 0 -> requires Loop ensures false;
 }
}

# x+y not bounded..

Termination checking result: 
(8)->(16) (MayTerm ERR: not bounded)[x+y]


 */
