data node {
	int val; 
	node left;
	node right;	
}


graph<v,M> == self = null & M = {}
	or self::node<0@M,l@L,r@L> & l::graph<0,Ml> & r::graph<0,Mr> & M = union(Ml,Mr,{self}) & v=0
	or self::node<0@M,l@L,r@L> & l::graph<_,Ml> & r::graph<_,Mr> & M = union(Ml,Mr,{self}) & v=1
	or self::node<1@I,l@L,r@L> & l::graph<2,Ml> & r::graph<2,Mr> & M = union(Ml,Mr,{self}) & v=2
	inv 0<=v<=2
	mem M->(node<@M,@L,@L> & 0<=v<=1 ; node<@I,@L,@L> & 1<=v<=2);

void mark(ref node x)
  requires x::graph<0,M>
  ensures x::graph<2,M>;
  requires x::graph<1,M>
  ensures x::graph<2,M>;
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
