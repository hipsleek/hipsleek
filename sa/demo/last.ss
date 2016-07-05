data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

lseg<p> == self = p & self!=null  or self::node<_, q> * q::lseg<p>& self!=p;
lshd<p> == p::lseg<self>*self::node<_,null>;

HeapPred H(node a).
HeapPred G(node a, node b).

node last (node x)
//requires x::ll<> & x!=null ensures res::lshd<x>;
infer[H,G] requires H(x) ensures G(res,x);
{
   if (x.next==null) return x;
   else 
   {
	node t = last(x.next);
	//t.val = t.val+1;
	//t.next = null;
	return t;
	}
}
/*
# last.ss

Relational Assumption:
======================
[ H(x)&true --> x::node<val_18_809,next_18_810>@M 
    * HP_1(next_18_810)&true,
 HP_1(next_18_810)&next_18_810!=null --> H(next_18_810)&true,
 HP_1(next_18_810)&next_18_810=null --> emp&true,
 x::node<val_18_809,next_18_810>@M&res=x & next_18_810=null 
   --> G(res,x)&true,
 x::node<val_18_809,next_18_810>@M * G(res,next_18_810)&
  next_18_810!=null --> G(res,x)&true]

Predicate:
==========
 H(x_828) ::=  x_828::node<val_18_809,next_18_810>@M 
      * HP_1(next_18_810)&true,
 G(res_830,x_831) ::=  
    res_830::node<val_18_809,next_18_810>@M&next_18_810=null & res_830=x_831
 or x_831::node<val_18_809,next_18_810>@M * G(res_830,next_18_810)&
    next_18_810!=null,
 HP_1(next_18_829) ::=  
   next_18_829::node<val_18_809,next_18_810>@M * HP_1(next_18_810)&true
 or emp&next_18_829=null

EXPECTING:
==========
 Need predicate-splitting to:
  G(res,x) <-> res::node<_,null>*P(x,res@NI)
 and then derive:
  P(x,res) = x=res
   x::node<_,q>*q::P<res>
*/


/*
{
   node y = x.next;
   if (y==null) return x;
   else {
     //assume false;
     node t = last(y);
     t.next=null;
     return t;
   }
}*/