
relation R(int x,int y,int a,int b).

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
    x = 2*x+y;
    y=y+1;
    loo(x,y);
  };
}

/*
# ex27b.ss 

  if (x>0) {
    x = 2*x+y;
    y=y+1;

# I guess the warning below can be downplayed
  as we had 2*x there which is later converted.

WARNING: _0:0_0:0:[omega.ml] Non-linear arithmetic is not supported by Omega.
push_list:[]

WARNING: _0:0_0:0:[omega.ml] Non-linear arithmetic is not supported by Omega.
push_list:[]

*/
