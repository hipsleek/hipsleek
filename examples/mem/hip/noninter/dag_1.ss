data node {
	int val; 
	node left;
	node right;	
}

dag<v,M> == self = null & M = {}
	or self::node<0@M,l@I,r@I> * l::dag<0,Ml> U* r::dag<0,Mr> & M = union(Ml,Mr,{self}) & v = 0
	or self::node<1@I,l@I,r@I> * l::dag<_,Ml> U* r::dag<_,Mr> & M = union(Ml,Mr,{self}) & v = 1
	inv true
	mem M->(node<@I,@I,@I> ; node<@M,@I,@I>);

void mark(ref node x)
requires x::dag<0,M>
//ensures x::dag<0,M>;  // fails
ensures x::dag<1,M>;
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
