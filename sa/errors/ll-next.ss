data node {
  int val;
  node next;
}

HeapPred H(node a).
HeapPred G(node a, node b).

/* return the tail of a singly linked list */
node get_next(node x)
  infer[H,G]
  requires H(x)
  ensures G(x,res);//'
{
  if (x==null) return null;
  return x.next;
}

node test (node x)
  requires x=null
  ensures res=null;
{
  return get_next(x);
}

/*
*************************************
**************case specs*************
*************************************
 case {
   x!=null -> 
     requires x::node<val,DP>@M & true
     ensures x1::node<val,res>@M & true;; 
   x=null -> 
     ensures emp & x1=null & res=null & res=x1;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(1;0) emp&x=null \/ (2;0) x::node<val,DP>@M,
 G(x,res) ::=(1;0) emp&x=null & res=null & res=x \/ (2;0) x::node<val,res>@M]
*************************************
*/
