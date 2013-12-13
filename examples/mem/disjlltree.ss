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

tree<p,S> == case {
  S={} -> [] self=null & S = {};
  S!={} -> [] self::node<_@L,_@A,p,l,r> * l::tree<self,Sl> * r::tree<self,Sr> & S = union(Sl,Sr,{self})
  & self!=p & p notin Sl & p notin Sr;}
  inv (self=null & S={} | self!=null & self in S) & p notin S
		memE S->(node<@L,@A,@M,@M,@M>);

lltree<v,p,S> == self = null & S = {}
	or self::node<_@L,n,_@A,_@A,_@A> * n::lltree<1,_,Sn> & S = union(Sn,{self}) & v = 1
	or self::node<_@L,_@A,p,l,r> * l::lltree<2,self,Sl> * r::lltree<2,self,Sr> & S = union(Sl,Sr,{self}) & v = 2;

global node q1s;
global node q1t;
global node q2;

node list_remove_first(ref node q1s)
requires q1s::ll<S>
ensures res::node<_@L,null,_@A,_@A,_@A> * q::ll<S1> & S = union(S1,{res}) & q1s' = q & q1s = res & res notin S1;

node tree_remove(node x, ref node q1t)
requires q1t::tree<p,S> * x::node<_@L,_,_@A,_@A,_@A>
ensures res::node<_@L,_@A,_@A,_@A,_@A> * q::tree<p,S1> & S = union({res},S1) & q1t' = q & res = x & res notin S1;

void delete_request(ref node q1s, ref node q1t)
requires q1s::ll<Sl> &* q1t::tree<p,St> & Sl = St
ensures q1s'::ll<Sl1> &* q1t'::tree<p,St1> & Sl = union(Sl1,{q1s}) & St = union(St1,{q1s}) & Sl1 = St1;
{
node c;
c = list_remove_first(q1s);
if (c == null) return;
tree_remove(c,q1t);
}

node list_remove_first2(ref node q1s)
requires q1s::lltree<1,_,S>
ensures res::node<_@L,null,_@A,_@A,_@A> * q::lltree<1,_,S1> & S = union(S1,{res}) & q1s' = q & q1s = res & res notin S1;

node tree_remove2(node x, ref node q1t)
requires q1t::lltree<2,p,S> * x::node<_@L,_,_@A,_@A,_@A>
ensures res::node<_@L,_@A,_@A,_@A,_@A> * q::lltree<2,p,S1> & S = union({res},S1) & q1t' = q & res = x & res notin S1;

void delete_request2(ref node q1s, ref node q1t)
requires q1s::lltree<1,_,S> * q1t::lltree<2,p,S>
ensures q1s'::lltree<1,_,S1> * q1t'::lltree<2,p,S1> & S = union(S1,{q1s});
{
node c;
c = list_remove_first2(q1s);
if (c == null) return;
tree_remove2(c,q1t);
}
