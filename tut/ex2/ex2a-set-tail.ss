data node{
  int val;
  node next;
}

void set_tail_fn(node x,node y)
  infer [@shape]  requires true ensures true;
{ 
  x.next=y;
}

/*
# ex2-set-tail.ss

void set_tail_fn(node x,node y)
  infer [P,Q]  requires P(x,y) ensures Q(x,y);
{ 
  x.next=y;
}

Can we print simplified pre/post spec?

!!! shape inference for flow:(4,5)
*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[ P(x_1365,y_1366) ::=  x_1365::node<val_14_1367,DP_DP_HP_1362>&y_1366=DP_DP_HP_1363,
 Q(x_1368,y_1369) ::=  x_1368::node<val_14_1370,y_1369>&y_1369=DP_DP_HP_1363]
*************************************


*/
