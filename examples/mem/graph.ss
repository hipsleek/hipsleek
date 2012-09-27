data node {
	int val; 
	node left;
	node right;	
}
//type error for self
graph<v,ann,M> == self = null & M = {}
	or (self::node<v@ann,l@L,r@L> & l::graph<v,ann,Ml> & r::graph<v,ann,Mr>) & M = union(Ml,Mr,{self})
	inv true
	mem M->(node<@M,@L,@L> | node<@A,@L,@L>);

void mark(ref node x)
requires x::graph<0,@M,M>
ensures x::graph<1,@A,M>;
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
