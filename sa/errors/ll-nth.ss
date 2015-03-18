data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

node nth(node x, int n)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  while (x != null)
    infer[H1,G1]
      requires H1(x)
      ensures G1(x,x');//'
    {
      if (n > 0)
        x = x.next;
      else
        break;
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
   DP=x & x=x' & x!=null -> 
     requires H1(next1) * x::node<val1,next1>@M & DP=x & x=x'
     ensures x1::node<val,next>@M * G1(next,x2) & true || emp & x1!=null & x1=x2;; 
   !(((x=null | (DP=x & x=x' & x!=null)))) -> ; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H1(x) ::=(1;1;0) x::node<val,next>@M * H1(next)&DP=x & x=x'
   \/ (2;0) emp&x=null,
 G1(x1,x) ::=(1;1;0) 
 x1::node<val,next>@M * G1(next,x)
 or emp&x1!=null & x=x1
 
   \/ (2;0) emp&x=x1 & x1=null & x=null]
*************************************

*************************************
**************case specs*************
*************************************
 case {
   true -> 
     requires x1::H1<> & true
     ensures x::G1<res> & true;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(0) x::H1<>@M,
 G(x,res) ::=(0) x::G1<res>@M]
*************************************
*/
