data node {
	int val; 
	node next;
	node left;
	node right;	
}


graph<v,M> == self = null // & M = {}
	or self::node<0,_@A,l,r> U* (l::graph<_,Ml> U* r::graph<_,Mr>) & v = 0
	//& M = union(Ml,Mr,{self}) 
	or self::node<1,_@A,l,r> U* (l::graph<1,Ml> U* r::graph<1,Mr>) & v = 1
	//& M = union(Ml,Mr,{self}) 
	inv true
	memE M->();
	//memE M->(node<@M,@A,@M,@M> & v = 0 ; node<1@M,@A,@M,@M> & v != 0);

ll<v,M> == self = null // & M = {}
	or self::node<0,p,_@A,_@A> * p::ll<0,Mp> & v = 0
	// & M = union(Mp,{self}) 
	or self::node<1,p,_@A,_@A> * p::ll<1,Mp> & v = 1
	// & M = union(Mp,{self}) 
	inv true
	memE M->();
	//memE M->(node<@M,@M,@A,@A> & v = 0 ; node<1@M,@M,@A,@A> & v != 0);


void mark(node x)
  requires x::graph<_,M>
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

void sweep(ref node free, node x, ref node p)
  requires free::ll<0,Mf> * (x::graph<1,M> U* p::ll<_,Mp>)
  ensures free'::ll<0,Mf2> * (x::graph<1,M> U* p'::ll<_,Mp2>);
{
//mark(x);
if(p == null) return;
else{
if(p.val != 1){ 
move(free,p);
}
else p = p.next;
if(p != null)
	sweep(free,x,p);
else return;
}
}

void move(ref node free, ref node p)
requires free::ll<0,Mf> * p::node<_,q,_@A,_@A> * q::ll<_,Mq>
ensures p::node<0,free,_@A,_@A> * free::ll<0,Mf> * q::ll<_,Mq> & p' = q & free' = p; 

void collect(ref node alloted, node x, ref node free)
  requires free::ll<0,Mf> * (x::graph<_,M> U* alloted::ll<_,Mp>)
  ensures free'::ll<0,Mf2> * (x::graph<1,M> U* alloted'::ll<_,Mp2>);
{
mark(x);
sweep(free,x,alloted);
}
  
