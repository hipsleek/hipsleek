data node {
	int val; 
	node left;
	node right;	
}


graph<v,M> == self = null // & M = {} 
	or self::node<0,l,r> & (l::graph<0,Ml> & r::graph<0,Mr>) & v=0
	// & M = union(Ml,Mr,{self}) 
	or self::node<0,l,r> & (l::graph<_,Ml> & r::graph<_,Mr>) & v=1
	// & M = union(Ml,Mr,{self}) 
	or self::node<1,l,r> & (l::graph<2,Ml> & r::graph<2,Mr>) & v=2
	// & M = union(Ml,Mr,{self}) 
	inv true
	memE M->();
	//memE M->(node<@M,@M,@M> & v!=2 ; node<1@M,@M,@M> & v = 2);
	
graph2<v,M> == self = null // & M = {}
	or self::node<0,l,r> * l::graph2<_,Ml> & r::graph2<_,Mr> & v = 0
	//& M = union(Ml,Mr,{self}) 
	or self::node<1,l,r> * l::graph2<1,Ml> & r::graph2<1,Mr> & v = 1
	//& M = union(Ml,Mr,{self}) 
	inv true
	memE M->();
	//memE M->(node<@M,@M,@M> & v = 0 ; node<1@M,@M,@M> & v != 0);	

void mark(ref node x)
  requires x::graph<0,M>
  ensures x::graph<2,M>;
  requires x::graph<_,M>
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

void mark2(ref node x)
  requires x::graph2<_,M>
  ensures x::graph2<1,M>;
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
