data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

relation Q(int a, int b, int c).

void append(node x, node y)
  infer [n,m,Q]
  requires x::ll<n> * y::ll<m> 
  ensures x::ll<e>& Q(n,m,e);
  requires x::ll<n> * y::ll<m> & n>0
  ensures x::ll<e>& e=n+m;
  requires x::lseg<r, n> * r::node<b,null>
{
  // dprint;
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
