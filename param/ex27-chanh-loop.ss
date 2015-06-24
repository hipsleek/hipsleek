
relation R(int x,int y,int a,int b).

void loo (int x, int y)
 case {
  x <= 0 -> requires Term ensures true;
  x > 0 -> case {
   x+y <= 0 -> requires Term[x] ensures true;
   x+y > 0 -> requires Loop ensures false;
  }
 }
{
  if (x>0) {
    x = 2*x+y;
    y=y+1;
    loo(x,y);
  };
}

/*
# ex27.ss 

while (x > 0) {
  x = 2*x + y;
  y = y + 1;
} 

Termination checking result: 
(8)->(16) (ERR: invalid transition)  Term[63; 1; x] ->  Loop{call 4:0}[]



 */
