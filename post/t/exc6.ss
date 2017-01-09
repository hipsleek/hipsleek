class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true; //  & flow __flow;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    //if (x>100) raise new Exp(2222);
    x=x-1;
    loop(x);
  } 
  return x;
}

/*
# exc6.ss

!!! REL POST :  post_1212(x,res)
!!! POST:  ((res=x-1 & 1<=x) | (res=x & x<=0))
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
loop$int
 requires emp & MayLoop[]
     ensures emp & ((res=x-1 & 1<=x) | (res=x & 
x<=0));



*/
