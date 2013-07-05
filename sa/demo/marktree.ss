data node {
 int val;
 node left;
 node right;
}

HeapPred H(node a).
HeapPred G(node a,int x).

tree<v> == self=null
 or self::node<0,p,q> * p::tree<0> * q::tree<0> & v = 0
 or self::node<0,p,q> * p::tree<_> * q::tree<_> & v = 1 
 or self::node<1,p,q> * p::tree<1> * q::tree<1> & v = 2
 inv true;

void mark(node x) 
/*
 requires x::tree<_>
 ensures x::tree<2>;
*/
 infer [H,G] 
 requires H(x)
 ensures G(x,2);
{
node l,r;
if(x == null) return;
else {
 if (x.val == 1) return;
 l = x.left;
 r = x.right;
 x.val = 1;
 mark(l);
 mark(r);
 }
}


