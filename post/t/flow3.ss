class Exp extends __Exc {
  int val;
}

void loop(ref int x)
  infer [@post_n]
  requires true
  ensures  true & flow __flow;
{
  if (x>0) {
    x = x-1;
    loop(x);
  } else {
    raise new Exp(2);
  }
}

/*
# flow3.ss

Got:
[RELDEFN post_1210(__norm#E): ( 0<=x_1227 & x=1+x_1227 & post_1210(x_1227,x')) -->  post_1210(x,x'),
RELDEFN post_1210(__norm#E): ( x=x' & x'<=0) -->  post_1210(x,x')]

Above may be OK since  __norm /\ __flow --> __norm


*************************************
[RELDEFN post_1210(__norm#E): ( 0<=x_1227 & x=1+x_1227 & post_1210(x_1227,x')) -->  post_1210(x,x'),
RELDEFN post_1210(__norm#E): ( x=x' & x'<=0) -->  post_1210(x,x')]
*************************************

!!! >>>>>> compute_fixpoint <<<<<<
!!! Input of fixcalc: post_1210:={[x] -> [PRIx] -> []: ((x=PRIx && PRIx<=0) || ( (exists (x_1227:(x_1227+1=x && post_1210(x_1227,PRIx))))  && 1<=x))
};

*/
