data node {
	int val; 
	node next;
	node left;
	node right;	
}


graph<v,M> == self = null & M = {}
	or self::node<0,_@A,l@L,r@L> * l::graph<_,Ml> & r::graph<_,Mr> & M = union(Ml,Mr,{self}) & v = 0
	or self::node<1@I,_@A,l@L,r@L> * l::graph<1,Ml> & r::graph<1,Mr> & M = union(Ml,Mr,{self}) & v = 1
	inv true
	mem M->(node<@M,@A,@L,@L> & v = 0 ; node<@I,@A,@L,@L> & v = 1);

ll<v,M> == self = null & M = {}
	or self::node<0@A,p,_@A,_@A> * p::ll<0,Mp> & M = union(Mp,{self}) & v = 0
	or self::node<1@A,p,_@A,_@A> * p::ll<1,Mp> & M = union(Mp,{self}) & v = 1
	inv true
	mem M->(node<@A,@M,@A,@A> & v = 0 ; node<@A,@M,@A,@A> & v = 1);


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

void sweep(node free, node x, node p)
  requires free::ll<0,Mf> * (x::graph<_,M> & p::ll<_,Mp>)
  ensures free::ll<0,Mf2> * (x::graph<1,M> & p::ll<_,Mp2>);
{
mark(x);
if(p.next == null) return;
else{
if(p.val != 1){ 
move(free,p);
}
sweep(free,x,p.next);
}
}

void move(node free, node p)
requires free::ll<0,Mf> * p::node<_@I,q,_@A,_@A> * q::ll<_,Mq>
ensures p::node<_@I,free,_@A,_@A> * free::ll<0,Mf> * q::ll<_,Mq>; 
