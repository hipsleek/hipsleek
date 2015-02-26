data node {
	int val;
	node next;
}

relation L(node x, int m). //Label
relation E(node x, node y). //Edge
relation U(node x, bag(node) S).

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

G<M,V,D,L,E> == self = null & D = {} 
	or self::node<m,p> * p::G<Mp,V,D,L,E> & self in V & m in D & L(self,m) & E(self,p)
	& M = union(Mp,{self})// & p in V
;//memE M->();

heap<R,S> == self = null & R = {} 
	or self::node<m,p> U* p::heap<Rp,S> & R = union(Rp,{self}) & self in S
memE R->(node<@M,@M>);

void append(node x, node y)
infer[x,y]
requires true
ensures true;
/*
infer[Rx,Ry,S]
requires x::heap<Rx,S> U* y::heap<Ry,S>
ensures true;

infer[Mx,My,V,D,L,E]
requires x::G<Mx,V,D,L,E> * y::G<My,V,D,L,E>
ensures true;

infer[n,m,p]
requires x::ll<n> * y::ll<m>
ensures x::ll<p>;
*/
{
	//debug on;
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
	//dprint;
		append(x.next, y);
		return;
	}
	else {	//debug on;
		//tmp.next = x;
		x.next = y;
		return;
	}
    //dprint;
}
   
