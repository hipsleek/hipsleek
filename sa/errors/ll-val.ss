data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, int b).

/* return the value of the first element */
  int get_val(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  if (x==null) return 0;
  else return x.val;
}

/*
*************************************
**************case specs*************
*************************************
 case {
   x!=null -> 
     requires x::node<val,DP>@M & true
     ensures x1::node<res,DP>@M & true;; 
   x=null -> 
     ensures emp & res=0 & x1=null;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(1;0) emp&x=null \/ (2;0) x::node<val,DP>@M,
 G(x,res) ::=(1;0) emp&res=0 & x=null \/ (2;0) x::node<res,DP>@M]
*************************************
*/
