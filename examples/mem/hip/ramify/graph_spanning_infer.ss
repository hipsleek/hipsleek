data node {
	int val; 
	node left;
	node right;	
}


graph<v,M> == self = null 
	// & M = {}
	or self::node<0,l,r> U* (l::graph<_,Ml> U* r::graph<_,Mr>) & v = 0
	// & M = union(Ml,Mr,{self}) 
	or self::node<1,l,r> U* (l::graph<1,Ml> U* r::graph<1,Mr>) & v = 1
	// & M = union(Ml,Mr,{self}) 
	inv true
	memE M->();
	//memE M->(node<@M,@M,@M> & v = 0 ; node<1@M,@M,@M> & v != 0);

tree<v,M> == self = null 
	// & M ={}
	or self::node<0,l,r> * l::tree<_,Ml> * r::tree<_,Mr> & v = 0
	// & M = union(Ml,Mr,{self}) 
	or self::node<1,l,r> * l::tree<1,Ml> * r::tree<1,Mr> & v = 1
	// & M = union(Ml,Mr,{self}) 
	inv true	
	memE M->();
	//memE M->(node<@M,@M,@M> & v = 0 ; node<1@M,@M,@M> & v != 0);

void spanning(node x)
requires x::graph<_,Mg> & Mg != {}
ensures x::tree<1,Mt> & Mt != {} & Mt subset Mg;
{
node l,r;
l = x.left;
r = x.right;
x.val = 1;
if(l != null){ 
	if(l.val == 0) spanning(l);
	else x.left = null;}
else x.left = null;
if(r != null){
	if(r.val == 0) spanning(r);
	else x.right = null;}
else x.right = null;
//dprint;
}
