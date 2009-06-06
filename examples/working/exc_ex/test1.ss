data node{int val;node next;}

list<z> == self::node<_,z>&z=null 
	or self::node<_,z>&z!=null
	or self::node<_,y>*y::list<z> inv 1>0;

coercion self::list<z>&z=null <- self::list<y>*y::list<z>&z=null;


node mod (node u, node v, node l)
requires u::list<v>*v::list<null>*l::node<_,v>
ensures res::list<null>;
{
	l.next = null;
	return u;
}

