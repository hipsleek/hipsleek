data node {
	int val;
	node next;
}

lseg<p, n> == self = p & n = 0
	or self::node<next = r> * r::lseg<p, m> & n = m + 1 & self != p
	inv n >= 0;

cl<n> == self = null & n = 0
	or self::node<next = r> * r::lseg<self, m> & n = m + 1
	inv n >= 0;

bool find(node l, node st, int v)
	requires l::lseg<st, n>
	ensures l::lseg<st, n>;
{
	if (l == null || l == st) return false;
	if (l.val == v) return true;
	return find(l.next, st, v);
}

void append(node x, node y)
	requires x::cl<n> * y::cl<m> & n > 0 & m > 0
//	ensures x::lseg<_, k> & k >= n;
	ensures x::cl<n + m>; // & y::cl<n + m>;
{
	node tmp = x.next;
	x.next = y.next;
	y.next = tmp;
}
