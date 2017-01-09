data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

  node find (node x, int d)
  infer[H,G]
  requires H(x)
     ensures G(x,res);
{
  while (x != null)
    infer[H1,G1]
      requires H1(x)
      ensures G1(x,x');//'
    {
      if (x.val == d)
        break;
      x = x.next;
    }
    return x;
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
     ensures x1::node<val,next>@M * G1(next,x2) & true || x2::node<val,next>@M * H1(next) & x1=x2;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H1(x) ::=(1;1;0) x::node<val,next>@M * H1(next) \/ (2;0) emp&x=null,
 G1(x1,x) ::=(1;1;0) 
 x1::node<val,next>@M * G1(next,x)
 or x::node<val,next>@M * H1(next)&x=x1
 
   \/ (2;0) emp&x=x1 & x1=null & x=null]
*************************************

*************************************
**************case specs*************
*************************************
 case {
   true -> 
     requires x1::H1<> & true
     ensures res::G1<x> & true;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(0) x::H1<>@M,
 G(x,res) ::=(0) res::G1<x>@M]
*************************************
*/
