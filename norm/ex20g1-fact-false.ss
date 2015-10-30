

HeapPred P(int x).

relation R(int x).

int fact(int i)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
//infer [P,@classic,@pure_field]
//  requires P(i)
  infer [R]
  requires R(i)
  ensures false;
{    
  if (i==0) return 1;
  else return i * fact(i-1);
}

/*
# ex20g1.ss 

[ // PRE_REC
(2;0)P(i@NI)&v_int_14_1499'+1=i & i!=0 --> emp&
true,
 // PRE_REC
(2;0)emp&i!=0 & v_int_14_1499'+1=i --> P(v_int_14_1499'@NI)&
true,
 // POST
P(i@NI)&true --> htrue&
i!=0]



*/
