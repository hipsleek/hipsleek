data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

/*
Why isn't 24-->30 decreasing?

Termination checking result:
(24)->(30) (ERR: not decreasing) Term[0; 0; n] -> Term[0; 0; n_665]
(24)->(30) (ERR: not decreasing) Term[0; 0; n] -> Term[0; 0; n_665]

Isn't x.next supposed to decrease the rank n?
is there a bug with substitution since n=n_665 from the
verbose printing?

*/

void append(node x, node y)
[
  requires x::ll<n> & Term[0,n] &x!=null //& n>0
  ensures x::lseg<y, n>;
  requires x::ll<n> & Term[0,n] & y=x & n>0
  ensures x::clist<n>;
]
{
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

