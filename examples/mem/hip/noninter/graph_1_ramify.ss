data node {
	int val; 
	node left;
	node right;	
}

graph<v,ann,M> == self = null & M = {}
	or self::node<v@ann,l@L,r@L> U* (l::graph<v,ann,Ml> U* r::graph<v,ann,Mr>) & M = union(Ml,Mr,{self}) & v = 0 
	or self::node<v@ann,l@L,r@L> U* (l::graph<v,ann,Ml> U* r::graph<v,ann,Mr>) & M = union(Ml,Mr,{self}) & v != 0
	inv true
	memE M->(node<@M,@L,@L> & v = 0 ; node<@A,@L,@L> & v != 0);

void mark(ref node x)
requires x::graph<_,@M,M>
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
