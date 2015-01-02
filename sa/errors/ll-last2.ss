data node {
  int val;
  node next;
}

ll<> == self::node<_,null> or self::node<_,p> * p::ll<>;

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

/* return the last element */
  node get_last(node x)
  
  infer[H,G]
  requires H(x)   ensures G(x,res);

{
  if (x.next == null) return x;
  return get_last(x.next);
}
/* else if (x.next == null) return x; */
/*   else return get_last(x.next); */

/*
*************************************
**************case specs*************
*************************************
 case {
   x!=null -> 
     requires x::node<val,next>@M * HP_934(next) & x!=null
     ensures x1::node<val,next>@M & x1=x2 & next=null || x1::node<val,next>@M * G1(next,x2) & next!=null;; 
   x=null -> ; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H1(x) ::=(1;0) x::node<val,next>@M * HP_934(next)&x!=null,
 G1(x1,x) ::=(1;0) 
 x1::node<val,next>@M&x=x1 & next=null
 or x1::node<val,next>@M * G1(next,x)&next!=null
 ,
 HP_934(next) ::=(1;0) 
 next::node<val,next1>@M * HP_934(next1)
 or emp&next=null
 ]
*************************************

*************************************
**************case specs*************
*************************************
 case {
   x=null -> 
     ensures emp & res=x1 & x1=null & res=null;; 
   x!=null -> 
     requires x::H1<> & x!=null
     ensures res::node<val_20_1056,next_20_1057>@M * x1::GP_977<res> & next_20_1057=null;; 
   }
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x) ::=(1;0) x::H1<>@M&x!=null \/ (2;0) emp&x=null,
 G(x,res) ::=(1;0) EXISTS(val_20_1056,next_20_1057: x::GP_977<res>@M * 
res::node<val_20_1056,next_20_1057>@M&next_20_1057=null)[]
   \/ (2;0) emp&res=x & x=null & res=null]
*************************************
*/
