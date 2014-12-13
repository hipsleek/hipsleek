data node{
  int val;
  node next;
}

void set_tail_fn(node x,node y)
  infer [@shape]  requires emp ensures emp;
{ 
  x.next=y;
}

/*
# ex2b-set-tail-emp.ss

How do we trigger a re-verification?
--reverify ?

However, this triggered an exception!

ExceptionInvalid_argument("List.combine")Occurred!

Error1(s) detected at main 
Stop Omega... 66 invocations caught

Exception occurred: Invalid_argument("List.combine")
Error3(s) detected at main 

-------

void set_tail_fn(node x,node y)
  infer [@shape]  requires emp ensures emp;

Seems like emp/emp is better.

!!! shape inference for flow:(4,5)
*********************************************************
*******relational definition (flow= (4,5))********
*********************************************************
[ HP_12(x_1366,y_1367) ::=  x_1366::node<val_9_1368,DP_DP_HP_1364>,
 GP_13(x_1369,y_1370) ::=  x_1369::node<val_9_1371,y_1370>]

*/
