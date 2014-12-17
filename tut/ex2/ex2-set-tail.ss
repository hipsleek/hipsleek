data node{
  int val;
  node next;
}

HeapPred P(node x,node y).
PostPred Q(node x,node y).

void set_tail_fn(node x,node y)
  infer [P,Q]  requires P(x,y) ensures Q(x,y);
{ 
  x.next=y;
}

/*
# ex2-set-tail.ss

This set-tail result is wrong. The previous one was correct.

[ P(x_1365,y_1366) ::= x_1365::node<val_12_1360,next_12_1361>&y_1366=DP_DP_HP_1363(4,5),
 Q(x_1367,y_1368) ::= P(x_1367,y_1368)(4,5)]

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
