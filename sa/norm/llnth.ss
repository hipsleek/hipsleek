data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

lseg<p> == self = p & self!=null  or self::node<_, q> * q::lseg<p>& self!=p;
lshd<p> == p::lseg<self>*self::node<_,null>;

HeapPred H(node a).
PostPred G(node a, node b).

  node last (node x, int n)
//requires x::ll<> & x!=null ensures res::lshd<x>;
infer[H,G] requires H(x) ensures G(res,x);
{
  if (n==0) return x;
   if (x==null) return null;
   else
   {
     return last (x.next, n-1);
   }
}


/*
 [ // BIND
(2;2;0)H(x)&x!=null --> x::node<val,next>@M * HP_947(next),
 // PRE_REC
(2;2;0)HP_947(next) --> H(next),
 // POST
(1;0)H(res)& res=x --> G(res,x),
 // POST
(1;2;0)H(x)&x=null & res=null --> G(res,x),
 // POST
(2;2;0)x::node<val,next>@M * G(res,next) --> G(res,x)]

************************************************

[ H(x) ::=(2;2;0) x::node<val,next>@M * H(next) \/ (1;2;0) emp&x=null
   \/ (1;0) DP_999(x),
 G(res,x) ::=(2;2;0) G(res,next) * x::node<val,next>@M
   \/ (1;2;0) emp&x=null & res=null & res=x \/ (1;0) DP_999(res)&res=x,
 DP_999(a) ::=(1;0) NONE]


 */
