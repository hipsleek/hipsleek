data node {
  int val;
  node next;
}


relation R(node x).

node hoo(node x)
  infer [@ana_ni]
  requires x>1
  ensures true;
{
  node y;
  dprint;
  y = y.next;
  return y;
}


/*
# ex2d.ss --ana-ni

  node y;
  dprint;
  y = y.next;

# Need to add y'>1 for each local var created;
  expects y'>1 at dprint

dprint(simpl): ex2c-ptr.ss:15: ctx:  
     emp&MayLoop[] & 1<x & x'=x&{FLOW,(4,5)=__norm#E}[]
 

*/


