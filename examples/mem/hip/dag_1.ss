data node {
	int val; 
	node left;
	node right;	
}

dag<v,ann,M> == self = null & M = {}
	or self::node<v@ann,l@L,r@L> * l::dag<v,ann,Ml> & r::dag<v,ann,Mr> & M = union(Ml,Mr,{self})
	inv true
	mem M->(node<@M,@L,@L> | node<@I,@L,@L>);

void mark(ref node x)
requires x::dag<0,@M,M>
ensures x::dag<1,@L,M>;
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
