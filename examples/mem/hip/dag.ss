data node {
	int val; 
	node left;
	node right;	
}


dag<v,M> == self = null & M = {} & v = 0
	or self::node<0@M,l@L,r@L> * l::dag<1,Ml> & r::dag<1,Mr> & M = union(Ml,Mr,{self}) & v=1
	or self::node<0@M,l@L,r@L> * l::dag<_,Ml> & r::dag<_,Mr> & M = union(Ml,Mr,{self}) & v=2
	or self::node<1@I,l@L,r@L> * l::dag<3,Ml> & r::dag<3,Mr> & M = union(Ml,Mr,{self}) & v=3
	inv 0<=v<=3
	mem M->(node<@M,@L,@L> & 1<=v<=2 ; node<@I,@L,@L> & 2<=v<=3);

void mark(ref node x)
  requires x::dag<1,M>
  ensures x::dag<3,M>;
  requires x::dag<2,M>
  ensures x::dag<3,M>;
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
