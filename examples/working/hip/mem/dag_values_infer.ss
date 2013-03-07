data node {
	int val; 
	node left;
	node right;	
}


dag<v,M> == self = null //& M = {}
	or self::node<0,l,r> * l::dag<0,Ml> & r::dag<0,Mr> & v=0 
	// & M = union(Ml,Mr,{self}) 
	or self::node<0,l,r> * l::dag<_,Ml> & r::dag<_,Mr> & v=1
	// & M = union(Ml,Mr,{self}) 
	or self::node<1,l,r> * l::dag<2,Ml> & r::dag<2,Mr> & v=2
	// & M = union(Ml,Mr,{self}) 
	inv true
        memE M->();
	//memE M->(node<@M,@M,@M> & v != 2 ; node<1@M,@M,@M> & v = 2);
	
dag2<v,M> == self = null //& M = {}
	or self::node<0,l,r> * l::dag2<_,Ml> & r::dag2<_,Mr> & v = 0
	// & M = union(Ml,Mr,{self}) 
	or self::node<1,l,r> * l::dag2<1,Ml> & r::dag2<1,Mr> & v = 1
	// & M = union(Ml,Mr,{self}) 
	inv true
	memE M->();
	//memE M->(node<@M,@M,@M> & v != 1 ; node<1@M,@M,@M> & v = 1);

void mark(ref node x)
  requires x::dag<0,M>
  ensures x::dag<2,M>;
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

