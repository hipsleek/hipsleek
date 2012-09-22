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
		memE S->(node<@L,@M,@A,@A,@A>);

tree<p,S> == self = null & S = {}
		or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tree<self,Sr> & S = union(Sl,Sr,{self}) 
		inv true
		memE S->(node<@L,@A,@M,@M,@M>);
		
treeseg<p,h,S> == self = h & S = {} & h != null
		or self::node<_@L,_@A,p,l,r> * l::treeseg<self,h,Sl> * r::tree<self,Sr> & h != self & h notin Sr & h notin Sl 
			& S = union(Sl,Sr,{self})
		or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::treeseg<self,h,Sr> & h != self & h notin Sl & h notin Sr
			& S = union(Sl,Sr,{self})
		inv h != null & h notin S
		memE S->(node<@L,@A,@M,@M,@M>);	

tseg<hd,S> == hd = self & S = {} & hd != null
	or self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tseg<hd,Sr> & hd in Sr & S = union({self},Sl,Sr)
	or self::node<_@L,_@A,p,l,r> * l::tseg<hd,Sl> * r::tree<self,Sr> & hd in Sl & S = union({self},Sl,Sr)
	inv hd != null
	memE S->(node<@L,@A,@M,@M,@M>);
		
lemma self::tree<p,S> -> self::treeseg<p,h,Ss> * h::node<_@L,_@A,_@M,_@M,_@M> & S = union(Ss,{h});

lemma self::tseg<hd,S> -> self::treeseg<_,hd,Ss> * hd::node<_@L,_@A,_@M,_@M,_@M> & S = union(Ss,{hd});

global node q1s;
global node q1t;
global node q2;

node list_remove_first(ref node q1s)
requires q1s::ll<S>
ensures res::node<_@L,q@M,_@A,_@A,_@A> * q::ll<S1> & S = union(S1,{res}) & q1s' = q & q1s = res;

void tree_remove(node x, ref node q1t)
requires q1t::treeseg<p,x,Ss> * x::node<_@L,_@A,_@M,_@M,_@M>
ensures q1t::tseg<x,Ss>;

void list_add_first(ref node q2, node y)
requires q2::ll<S> * y::node<v@L,_@M,_@A,_@A,_@A>
ensures  y::node<v@L,q2@A,_@A,_@A,_@A> * q2::ll<S> & q2' = y;

void tree_add(ref node q1t, node y)
requires q1t::tree<p,S> * y::node<v@L,_@A,_,_,_>
ensures q1t::tree<p,S1> & S1 = union(S,{y});

void totree(ref node q1s, ref node q1t)
requires q1s::ll<S>
ensures q1t::tree<p,S>;

void move_request(ref node q1s, ref node q2, ref node q1t)
requires (q1s::ll<S> & q1t::tseg<q1s,S> * q2::ll<Sq>)
ensures (q1s'::ll<S1> & q1t::tseg<q1s',S1> * q2'::ll<Sq1>) & S = union(S1,{q1s}) & Sq1 = union(Sq,{q1s});
{
node c;
c = list_remove_first(q1s);
if (c == null) return;
tree_remove(c,q1t);
list_add_first(q2,c);
}
