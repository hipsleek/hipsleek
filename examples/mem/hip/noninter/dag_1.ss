data node {
	int val; 
	node left;
	node right;	
}

dag<v,ann,M> == self = null & M = {}
	or self::node<v@ann,l@I,r@I> * l::dag<v,ann,Ml> U* r::dag<v,ann,Mr> & M = union(Ml,Mr,{self})
	inv true
	mem M->(node<@A,@I,@I> ; node<@M,@I,@I>);

void mark(ref node x)
requires x::dag<0,@M,M>
ensures x::dag<1,@A,M>;
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
