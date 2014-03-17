data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a).

/* return the tail of a singly linked list */
  int get_size(node x)
  infer[H,G]
  requires H(x)
     ensures G(x);
{
  if(x == null) 
    return 0;
  else {
    return get_size(x.next) + 1;
  }
}

/*
*************************************
**************case specs*************
*************************************
 case {
   x!=null -> 
     requires H(next1) * x::node<val1,next1>@M & true
     ensures x1::node<val,next>@M * G(next) & true;; 
   x=null -> 
     ensures emp & x1=null;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(1;0) emp&x=null \/ (2;0) x::node<val,next>@M * H(next),
 G(x) ::=(1;0) emp&x=null \/ (2;0) x::node<val,next>@M * G(next)]
*************************************
*/
