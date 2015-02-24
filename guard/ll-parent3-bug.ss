// simpler tll working example

data node{
	node parent;
	node right;
}

tree<> == self::node<_,null>
        or self::node<p,r> * r::tree<>
	inv self!=null;

treep<p> == self::node<p,null>
        or self::node<p,r> * r::treep<self>
	inv self!=null;



// initializes the linked list fields

HeapPred H( node a).
HeapPred G(node@NI p, node a).

void trav ( node x)
  infer [H,G] requires H(x) ensures G(p,x);
                             //requires x::tree<> ensures x::treep<p>;
{
  if (x.right!=null) 
  	{
          trav(x.right);
          x.right.parent = x;

}
}

/*
# tll.ss --sa-dnc --pred-en-dangling --pred-en-eup

[ // BIND
(0)H(p@NI,x) --> x::node<parent_22_923,right_22_924>@M * 
   HP_925(parent_22_923,p@NI) * 
   HP_926(right_22_924,p@NI),

 H(p@NI,x) --> x::node<p,q>@M * HP_926(q,p@NI),

 // PRE_REC
 HP_926(q,p@NI)&q!=null |#| xx::node<p,q>@M --> H(xx@NI,q),

 // POST
(1;0)HP_925(parent_22_923,p@NI) * x::node<p,right_22_924>@M * 
G(x@NI,right_22_924)&right_22_924!=null & 
p=parent_22_923 --> G(p@NI,x),

 HP_925(parent_22_923,p@NI) & p=parent_22_923  --> true
 x::node<p,right_22_924>@M * G(x@NI,right_22_924)&right_22_924!=null 
     --> G(p@NI,x),

// POST
(2;0)HP_925(parent_22_923,p@NI) * HP_926(right_22_924,p@NI) * 
x::node<p,right_22_924>@M&right_22_924=null & 
p=parent_22_923 --> G(p@NI,x)]

 HP_925(parent_22_923,p@NI) & p=parent_22_923 --> true

 HP_926(r,p@NI) & r=null --> true

 x::node<p,right_22_924>@M&right_22_924=null  --> G(p@NI,x)]

=====

 HP_926(right_22_924,p@NI) & right_22_924=null --> true

 HP_926(right_22_924,p@NI)&right_22_924!=null
      |#| xx::node<p,right_22_924>@M --> H(xx@NI,right_22_924),

 HP_926(r,p@NI)&r!=null |#| xx::node<p,r>@M --> H(xx@NI,r),

 HP_926(r,p@NI)&r!=null |#| xx::node<p,r>@M --> 
                r::node<?,q>@M * HP_926(q,?@NI),

HP_926(r,p@NI)&r!=null |#| xx::node<p,r>@M --> 
                r::node<p,q>@M * HP_926(q,r@NI),

 HP_926(r,p@NI)&r!=null  --> 
      r::node<p,q>@M * HP_926(q,r),

 HP_926(r,p@NI)&r!=null --> r::node<p,q>*q::HP_926(q,r)


=============================================
 H(p@NI,x) --> x::node<p,q>@M * HP_926(q,p@NI),
 HP_926(right_22_924,p@NI) & right_22_924=null --> true,
 HP_926(q,p@NI)&r!=null |#| xx::node<p,q>@M --> H(xx@NI,q),

====================================
1. Freeze HP_926

2. Transform H by unfolding HP_926
 (i) H(p@NI,x) --> x::node<p,null>@M ,
 (ii) H(p@NI,x) --> x::node<p,q>@M * HP_926(q,p@NI) & q!=null,

   H(p@NI,x) --> x::node<p,q>@M * (H(xx@NI,q) |#|  xx::node<p,q>) & q!=null

   H(p@NI,x) --> x::node<p,q>@M * H(x@NI,q) & q!=null

-------------------------------

[ // BIND
(0)H(p@NI,x) --> x::node<parent_22_923,right_22_924>@M * 
HP_925(parent_22_923,p@NI) * 
HP_926(right_22_924,p@NI),
 // PRE_REC
(1;0)HP_926(right_22_924,p@NI)&right_22_924!=null & 
p=parent_22_923 |#| x::node<p,right_22_924>@M --> H(x@NI,right_22_924),
 // POST
(1;0)HP_925(parent_22_923,p@NI) * x::node<p,right_22_924>@M * 
G(x@NI,right_22_924)&right_22_924!=null & 
p=parent_22_923 --> G(p@NI,x),
 // POST
(2;0)HP_925(parent_22_923,p@NI) * HP_926(right_22_924,p@NI) * 
x::node<p,right_22_924>@M&right_22_924=null & 
p=parent_22_923 --> G(p@NI,x)]

--sa-dnc

Why isn't HP_925 dropped?
Why isn't p_951=parent_22_923 in H(..)?

[ G(p_953,x_954) ::=(1;0) 
 HP_925(parent_22_923,p_953) * x_954::node<p_953,right_22_924>@M * 
  G(x_954,right_22_924)&right_22_924!=null & p_953=parent_22_923
   \/ (2;0) HP_925(parent_22_923,p_953) * x_954::node<p_953,right_22_924>@M&
p_953=parent_22_923 & right_22_924=null,

 H(p_951,x_952) ::=(1;0) x_952::node<parent_22_923,right_22_924>@M 
      * HP_925(parent_22_923,p_951) * H(x_952,right_22_924)
        &right_22_924!=null
   \/ (2;0) x_952::node<parent_22_923,right_22_924>@M 
       * HP_925(parent_22_923,p_951) & right_22_924=null,

 HP_925(parent_22_923,p) ::= htrue]

without --sa-dnc

[ G(p_957,x_958) ::= 
 HP_925(p_957,p_957) * x_958::node<p_957,right_22_924>@M * 
 G(x_958,right_22_924)&right_22_924!=null
 or HP_925(p_957,p_957) * x_958::node<p_957,right_22_924>@M&right_22_924=null
 ,
 H(p_955,x_956) ::= 
 x_956::node<parent_22_923,right_22_924>@M * HP_925(parent_22_923,p_955) * 
 H(x_956,right_22_924)&right_22_924!=null
 or x_956::node<parent_22_923,right_22_924>@M * HP_925(parent_22_923,p_955)&
    right_22_924=null
 ,
 HP_925(parent_22_923,p) ::= NONE]

*/
