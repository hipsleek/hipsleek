class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures  true & flow __flow;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{

    raise new Exp(888);
    loop(x);
}

/*
# exc5.ss

*************************************
[RELDEFN post_1209(Exp#E): ( res=888) -->  post_1209(x,res)]
*************************************

We need to filter out exceptional flow, before passing
it for fix-point computation; and then adding back
as separate exceptional flow.

[( post_1209(x,res), res=888, true, true)]
 

Instead of:

Post Inference result:
loop$int
 requires emp & MayLoop[]
 ensures emp & res=888;

Should be:
requires emp & MayLoop[]
 ensures emp & res=888 & flow __Exp;


*/
