data node {
	int val; 
	node left;
	node right;	
}


dag<v,M> == self = null & M = {}
	or self::node<0,l@L,r@L> * l::dag<0,Ml> U* r::dag<0,Mr> & M = union(Ml,Mr,{self}) & v=0
	or self::node<0,l@L,r@L> * l::dag<_,Ml> U* r::dag<_,Mr> & M = union(Ml,Mr,{self}) & v=1
	or self::node<1@I,l@L,r@L> * l::dag<2,Ml> U* r::dag<2,Mr> & M = union(Ml,Mr,{self}) & v=2
	inv true
	memE M->(node<@M,@L,@L> & 0<=v<=1 ; node<@I,@L,@L> & 1<=v<=2; node<@M,@M,@M> & v < 0; node<@M,@M,@M> & v > 2 );
	
dag2<v,M> == self = null & M = {}
	or self::node<0,l@L,r@L> * l::dag2<_,Ml> U* r::dag2<_,Mr> & M = union(Ml,Mr,{self}) & v = 0
	or self::node<1@I,l@L,r@L> * l::dag2<1,Ml> U* r::dag2<1,Mr> & M = union(Ml,Mr,{self}) & v = 1
	inv true
	memE M->(node<@M,@L,@L> & v = 0 ; node<@I,@L,@L> & v != 0);

void mark(ref node x)
//requires x::dag<0,M>
//ensures x::dag<2,M>;
  requires x::dag<_,M>
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

void mark2(ref node x)
  requires x::dag2<_,M>
  ensures x::dag2<1,M>;
{
node l,r;
if(x == null) return;
else {
if (x.val == 1) return;
l = x.left;
r = x.right;
x.val = 1;
mark2(l);
mark2(r);
}
}

