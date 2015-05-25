data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

relation P(int a,int b,int c).

void append(node x, node y)
  infer [P]
  requires x::ll<n> * y::ll<m> & n>0
  ensures x::ll<e> & P(e,n,m); //e=n+m;
{
	if (x.next!=null) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}
