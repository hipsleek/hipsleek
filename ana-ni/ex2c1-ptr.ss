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
  node y = x.next;
  dprint;
  //y = null;
  y.next = null;
  dprint;
  return y;
}


/*
# ex2c.ss -p hoo

# Need to add next_15_1687' into the heap-state; so that we 
  have y'>1 at dprint.

dprint(simpl): ex2c-ptr.ss: 15: ctx:  
     emp&1<x & x'=x&{FLOW,(4,5)=__norm#E}[]


!!! **typechecker.ml#1968:vs_prim:[val_15_1686',next_15_1687']
!!! **typechecker.ml#1969:vheap(0): y'::node<val_15_1686',next_15_1687'>@L&{FLOW,(1,28)=__flow#E}[]
!!! **typechecker.ml#2015:need to use local version of infer_const_obj

*/


