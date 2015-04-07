//@ relation P1(int a, int b).
//@ relation P2(int a, int b).

//@ relation P3(int a).
//@ relation P4(int a).

int id(int x)
/* infer[P1,P2]
  case {
  x>=0 & x<=3 -> ensures emp & P1(res,x);
  x>3 -> ensures emp &  P2(res,x);
  x<0 -> requires Loop ensures false;
  }
 */
/* infer[P1,P3,P2]
   requires P3(x) ensures emp & P1(x,res) & res=3 or emp & P2(x,res) & res<3;
 */
/*@ infer[@pre_n,@post_n]
  requires  emp & true
  ensures emp & true;
 */
{

  if (x==0) return 0;
  int ret = id(x-1) + 1;
  if (ret > 3) return 3;
  return ret;

  /*
  if (x==0) return 0;
  int ret1;
  
  if (x-1==0) ret1= 0+1;
  int ret2 = id(x-1-1) + 1;
  if (ret2 > 3) ret1 = 3;
  ret1= ret2;

  if (ret1 > 3) return 3;
  return ret1;
  */
}

/*
!!! **pi.ml#631:fixpoint:[( post_1441(x,res,flow), res>=0 & x>=res, pre_1440(x), 0<=x)]
 */
