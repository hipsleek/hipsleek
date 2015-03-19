data node {
  int val;
  node prev;
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
  else return x.next;
}

/*
*************************************
**************case specs*************
*************************************
 case {
   x!=null ->
     requires x::node<val,DP,DP1>@M & true
     ensures x1::node<val,DP,res>@M & true;; 
   x=null -> 
     ensures emp & x1=null & res=null & res=x1;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(1;0) emp&x=null \/ (2;0) x::node<val,DP1,DP>@M,
 G(x,res) ::=(1;0) emp&x=null & res=null & res=x
   \/ (2;0) x::node<val,DP,res>@M]
*************************************
*/
