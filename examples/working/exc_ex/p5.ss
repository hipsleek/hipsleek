data node{int v; node next;}

ll<y> == self::node<_,y>
	or self::node<_,z>*z::ll<y>;

node change(node l, node u)

requires u::ll<x>*x::ll<null>*l::node<_,x>

ensures res::ll<null>;

{
	l.next = null;
	return l;
}
