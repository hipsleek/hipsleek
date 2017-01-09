data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

/* return the last element */
  node get_last(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  node prev = null;

  while (x != null)
    infer[H1,G1]
      requires H1(x)
      ensures G1(x,x');//'
    {
      node next = x.next;
      x.next = prev;
      prev = x;
      x = next;
    }
  return prev;
}

/*
*************************************
**************case specs*************
*************************************
 case {
   x=null -> 
     ensures emp & x1=x2 & x1=null & x2=null;; 
   x!=null -> 
     requires H1(next1) * x::node<val1,next1>@M & true
     ensures x1::node<val,prev>@M * G1(next,x2) & true;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H1(x) ::=(1;0) x::node<val,next>@M * H1(next) \/ (2;0) emp&x=null,
 G1(x1,x) ::=(1;0) x1::node<val,prev>@M * G1(next,x)
   \/ (2;0) emp&x=x1 & x1=null & x=null]
*************************************

*************************************
**************case specs*************
*************************************
 case {
   true -> 
     requires x::H1<> & true
     ensures emp & true;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(0) x::H1<>@M,
 G(x,res) ::=(0) emp]
*************************************

*/
