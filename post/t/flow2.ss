class Exp extends __Exc {
  int val;
}

void loop(ref int x)
  infer [@post_n]
  requires true
  ensures  true & flow __flow;
{
  if (x>0) {
    /* raise new Exp(2); */
    x = x-1;
    loop(x);
  } else {
    return;
  }
}

/*
# flow2.ss

Got:
[RELDEFN post_1210(__norm#E): ( 0<=x_1227 & x=1+x_1227 & post_1210(x_1227,x')) -->  post_1210(x,x'),
RELDEFN post_1210(__norm#E): ( x=x' & x'<=0) -->  post_1210(x,x')]

Expecting:
[RELDEFN post_1210: ( 0<=x_1227 & x=1+x_1227 & post_1210(x_1227,x')) -->  post_1210(x,x'), (#which denotes __flow)

Problem is at check_post, since we got __norm rather than __flow.

check_pre_post(2)@3 EXIT: List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]

Successful States:
[
 Label: [(,0 ); (,1 )]
 State:(exists x_1226: emp&0<x_1223 & x_1223=x & v_bool_10_1193' & 0<x_1223 & v_bool_10_1193' & x_1226+1=x_1223 & post_1210(x_1226,x')&{FLOW,(4,5)=__norm#E})[]

 ]
   ]

*/
