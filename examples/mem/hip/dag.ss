data node {
	int val; 
	node left;
	node right;	
}

dag<v,ann,M> == self = null & M = {}
	or (self::node<v@ann,l@L,r@L> * l::dag<v,ann,Ml> & r::dag<v,ann,Mr>) & M = union(Ml,Mr,{self})
	inv true
	mem M->(node<0@M,@L,@L> | node<1@I,@L,@L>);

/*
dag<v,M> == self = null & M = {}
	or (self::node<0@M,l@L,r@L> * l::dag<2,Ml> & r::dag<2,Mr>) & M = union(Ml,Mr,{self}) & v=0
	or (self::node<0@M,l@L,r@L> * l::dag<_,Ml> & r::dag<_,Mr>) & M = union(Ml,Mr,{self}) & v=1
	or (self::node<1@I,l@L,r@L> * l::dag<1,Ml> & r::dag<1,Mr>) & M = union(Ml,Mr,{self}) & v=2
	inv 0<=v<=2
	mem M->(node<0@M,@L,@L> & (0<=v<=1) | node<1@I,@L,@L> & 1<=v<=2);

*/

void mark(ref node x)
  requires x::dag<0,M>
  ensures x::dag<2,M>;
  requires x::dag<1,M>
  ensures x::dag<2,M>;
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
