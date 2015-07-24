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
PHASE 1
1. pre_1440(x) & x=1+v_int_25_1413' & (v_int_25_1413'+1)!=0 -->  pre_1440(v_int_25_1413')

2. (v_int_25_1465+1)!=0 & 3<=tmp' & res=3 & x=1+v_int_25_1465 & pre_1440(x) & post_1441(v_int_25_1465,tmp',flow) -->  post_1441(x,res,flow),

3. x=0 & res=0 & pre_1440(x)) -->  post_1441(x,res,flow),

4. (v_int_25_1465+1)!=0 & tmp_1478<=2 & res=1+tmp_1478 & x=1+v_int_25_1465 &
pre_1440(x) & post_1441(v_int_25_1465,tmp_1478,flow) -->  post_1441(x,res,flow)



!!! **pi.ml#631:fixpoint:[( post_1441(x,res,flow), res>=0 & x>=res, pre_1440(x), 0<=x)]
 */
