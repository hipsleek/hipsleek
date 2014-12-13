data node{
  int val;
  node next;
}

HeapPred P(node x).
  PostPred Q(node x,node y).

node tail_fn(node x)
  infer [P,Q]
  requires P(x) 
  ensures Q(x,res);
{ 
  return x.next;
}

/*
# ex1-get-tail.ss

--sa-en-pure-field

For pure field, can we do a similar conversion
as dangling ptr, so that we get something like:

[ P(x_1365) ::=  x_1365::node<DP_val_1361,DP_DP_HP_1362>
 Q(x_1367,res_1368) ::=  x_1367::node<DP_val_1361,res_1368>&res_1368=DP_DP_HP_1362]


!!! shape inference for flow:(4,5)
*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[ P(x_1365) ::=  x_1365::node<val_14_1366,DP_DP_HP_1362> * HP_1361(val_14_1359),
 Q(x_1367,res_1368) ::=  HP_1361(val_14_1359) * x_1367::node<val_14_1369,res_1368>&
res_1368=DP_DP_HP_1362]

----------

What is flow(4,5) - norm?
Can we print the inferred pre/post spec?
Currently the int value is not preserved.
Is there a way to preserve it or do we need @L?

!!! shape inference for flow:(4,5)
*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[ P(x_1364) ::=  x_1364::node<val_15_1365,DP_DP_HP_1361>,
 Q(x_1366,res_1367) ::=  x_1366::node<val_15_1368,res_1367>&res_1367=DP_DP_HP_1361]

*/
