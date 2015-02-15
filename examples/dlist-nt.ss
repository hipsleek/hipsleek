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

/* right to left proof */
void prove_coer3(node x)
	requires x::dsegN<s, p, t, r> * t::node<_, r, n> & x != n & p != t
	ensures x::dsegN<s+1, p, n, t>;
{
	unfold x';
}


void prove_coer2(node x, node n)
	requires x::dsegN<s, p, n, t> & x != n
	ensures x::dsegN<s - 1, p, t, r> * t::node<_, r, n>;
{
//dprint graph;
	unfold x';
//dprint graph;
	node tmp = x.next;
//dprint graph;
//debug on;
//dprint graph;

	if (tmp == n) {
//dprint graph;
		unfold tmp';
//dprint graph;
		return;
	}
	else {
dprint graph;
		return;
	}
//	if (s == 1) {
//dprint graph;
//		return;
//	}
//	else {
//dprint graph;
//		return;
//	}
}



// delete circular

void delete_cir(ref node x)
	requires x::dcl<s> & x != null
	ensures x'::dcl<s-1>;
{
	if (x.next == x) {
		x = null;
		return;
	}
	else {
		node tmp = x.prev;
		tmp.next = x.next;
		x.next.prev = x.prev;
		x = x.next;
//dprint aa;
		if (x.next == x) {} else {}
//		unfold x;
//dprint aa;
		return;

/*
		if (x.next == x) {
dprint aa;
//debug on;
			return;
//debug off;
		}
		else {
			return;
		}
*/
	}
}

void test2(node x)
	requires x::node<_,_,_>
	ensures x::dcl<_>;
{
	x.next = x;
	x.prev = x;
}

/*
// insert element after x
void insert(node x, node v)
        requires x::dcl<> * v::node<_,_,_> & x != null
        ensures x::dcl<>;
{
        v.next = x.next;
        x.next.prev = v;
        x.next = v;
        v.prev = x;
}

// delete element after x

void delete1(ref node x)
        requires x::dcl<> & x != null
        ensures x'::dcl<>;
{
        if (x.next == x) x = null;
        else {
                node tmp = x.next.next;
                x.next = tmp;
                tmp.prev = x;
        }
}

*/

void test(node x)
{
	node y, z;
	y = new node(2, null, null);
	z = new node(3, null, null);
	x = new node(1, y, z);
dprint;
dprint abc;
}

void test1(ref node x)
	requires x::ll<n> & x != null
	ensures x'::ll<n-1>;
{
	if (x.next == null) {
dprint;
assert n=1;
		x = null;
	}
	else {
		assume false;
	}
}
