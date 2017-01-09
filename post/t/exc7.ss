class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true  & flow __flow;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    //dprint;
    if (x>100) raise new Exp(2222);
    else raise new Exp(3333);
    loop(x);
  } 
  //else {return x+1;}
  // dprint;
  return x+1111;
}

/*
# exc7.ss

Obtained:

[RELDEFN post_1219(Exp#E): ( res=2222 & 101<=x) -->  post_1219(x,res),
RELDEFN post_1219(Exp#E): ( res=3333 & 1<=x & x<=100) -->  post_1219(x,res)]

Display below can be improved:

!!! cat:RELDEFN post_1219(Exp#E)
!!! pf: res=3333 & 1<=x & x<=100
!!! cat:RELDEFN post_1219(Exp#E)
!!! pf: res=2222 & 101<=x

Also, post cond still missing o Exp specs:

Post Inference result:
loop$int
 requires emp & MayLoop[]
     ensures emp & res=x+1111 & x<=0;


*/
