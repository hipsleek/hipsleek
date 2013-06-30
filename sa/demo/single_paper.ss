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
       node v = t.next;
       dprint;
       assert v' = null;
       return t;
       }
}
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
