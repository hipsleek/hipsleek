class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true ;
 // & flow __flow;
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
# exc8.ss

 infer [@post_n]
  requires true
  ensures true ;

Why is there post inference despite the failure
of post-condition proving? This should not happen.

Obtained:

Exception Failure("Post condition cannot be derived.") Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure loop$int

*************************************
***pure relation assumption (norm)***
*************************************
[RELDEFN post_1219: ( x+1111=res & res<=1111) -->  post_1219(x,res)]
*************************************

*************************************
*******fixcalc of pure relation *******
*************************************
[( post_1219(x,res), res=x+1111 & x<=0, true, true)]
*************************************

!!! REL POST :  post_1219(x,res)
!!! POST:  res=x+1111 & x<=0
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
loop$int
 requires emp & MayLoop[]
     ensures emp & res=x+1111 & x<=0;


*/
