

int loop(int x)
 infer [@post_n]
  requires true
//ensures true & flow __norm; //for pre-post assume
  ensures true & flow __flow;  //for post-cond
{
    //if (x>100) raise new Exp(2222);
    x=x-1;
    loop(x);
    return x;
}

/*
# exc6f.ss


[RELDEFN post_1174: ( x=1+res & post_1174(res,v_int_10_1184)) 
       -->  post_1174(x,res)]

 infer [@post_n]
  requires true
  ensures true & flow __flow;

Why did we not trigger any post-cond inference?
However, exc6.ss did not have any problem.

!!!Full processing file "exc6a.ss"
Parsing file "exc6a.ss" by default parser...

!!! processing primitives "["prelude.ss"]
Starting z3... 

Checking procedure loop$int... 
Procedure loop$int SUCCESS.
Stop z3... 37 invocations 
0 false contexts at: ()

# exc6.ss results:

 infer [@post_n]
  requires true
  ensures true 

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
