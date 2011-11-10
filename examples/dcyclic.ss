data node {
        int val;
        node prev;
        node next;
}

ll<n> == self = null & n=0
	or self::node<_,_,r> * r::ll<n-1>
	inv n>=0;

dsegN<s, p, n, t> == self = n & p = t & s = 0
        or self::node<_, p, r> * r::dsegN<s - 1, self, n, t> & self != n & p != t
	inv s >= 0;

dcl<s> == self = null & s = 0
        or self::node<_, r1, r2> * r2::dsegN<s - 1,self, self, r1>
	inv s >= 0;

//lemma "coer1" self::dsegN<p, n, t> <-> t::dsegP<self, p, n>;

lemma "coer2" self::dsegN<s, p, n, t> & self != n 
	-> self::dsegN<s - 1, p, t, r> * t::node<_, r, n>;

//lemma "coer3" self::dsegN<s, p, t, r> * t::node<_, r, n> & self != n & p != t
//	-> self::dsegN<s + 1, p, n, t>;

/*
	find a node

	st: sentinel
*/
node find(node l, node st, int v)
/*
	requires l::dcl<s>
	ensures l::dcl<s> & res::dcl<s>
		or l::dcl<s> & res = null;
*/
	requires l::lseg<
{
	if (l == st || l == null) return null;
	if (l.val == v) return l;
	node tmp = find(l.next, st, v);
	return tmp;
}
