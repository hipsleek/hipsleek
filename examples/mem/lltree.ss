data node {
	int val; 
	node next;
	node parent;
	node left;
	node right;	
}

ll<S> == self = null & S = {}
		or self::node<_@L,n,_@A,_@A,_@A> * n::ll<Sn> & S = union(Sn,{self})
		inv true
		mem S->(node<@L,@M,@A,@A,@A>);

tree<p,S> == self = null & S = {}
		or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tree<self,Sr> & S = union(Sl,Sr,{self}) 
		inv true
		mem S->(node<@L,@A,@M,@M,@M>);

global node q1s;
global node q1t;
global node q2;

node list_remove_first(ref node q1s)
requires q1s::ll<S>
ensures res::node<_@L,_@M,_@A,_@A,_@A> * q::ll<S1> & S = union(S1,{res}) & q1s' = q & q1s = res;

void tree_remove(node x, ref node q1t)
requires x::node<_@L,_@A,_@M,_@M,_@M> * q1t::tree<_,S>
ensures q1t::tree<_,S1> & S = union(S1,{x});

void list_add_first(ref node q2, node y)
requires q2::ll<S> * y::node<v,_,_@A,_@A,_@A>
ensures  y::node<v,q2,_@A,_@A,_@A> * q2::ll<S> & q2' = y;

void tree_add(ref node q1t, node y)
requires q1t::tree<p,S> * y::node<v,_@A,_,_,_>
ensures q1t::tree<p,S1> & S1 = union(S,{y});

void totree(ref node q1s, ref node q1t)
requires q1s::ll<S>
ensures q1t::tree<_,S>;

void move_request(ref node q1s, ref node q2, ref node q1t)
requires (q1s::ll<S1> & q1t::tree<_,S1> * q2::ll<S2>)
ensures (q1s::ll<S1a> & q1t::tree<_,S1a> * q2::ll<S2a>) & S1 = union(S1a,{q1s}) & S2a = union(S2,{q1s});
{
node c;
c = list_remove_first(q1s);
if (c == null) return;
tree_remove(c,q1t);
list_add_first(q2,c);
c = null;
}
