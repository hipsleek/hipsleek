// runs with --ramify option to prevent duplicate pointer unfolding

data node {
	int val; 
	node left;
	node right;	
}

graph<v,M> == self = null & M = {}
	or self::node<0,l@I,r@I> U* (l::graph<0,Ml> U* r::graph<0,Mr>) & M = union(Ml,Mr,{self}) & v = 0
	or self::node<1,l@I,r@I> U* (l::graph<_,Ml> U* r::graph<_,Mr>) & M = union(Ml,Mr,{self}) & v = 2
	or self::node<1,l@I,r@I> U* (l::graph<1,Ml> U* r::graph<1,Mr>) & M = union(Ml,Mr,{self}) & v = 1
	inv true
	mem M->(node<@M,@I,@I> ; node<@I,@I,@I>);

void mark(ref node x)
requires x::graph<0,M>
//ensures x::graph<_,M>; //fails
ensures x::graph<1,M>;
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
