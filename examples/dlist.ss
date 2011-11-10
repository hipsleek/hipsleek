data node {
        int val;
        node prev;
        node next;
}

ll<n> == self = null & n=0
	or self::node<_,_,r> * r::ll<n-1>
	inv n>=0;

dsegN<s, p, n, t> == self = n & p = t & s = 0
        or self::node<_, p, r> * r::dsegN<s - 1, self, n, t>
	inv s >= 0;

dsegP<s, f, p, n> == self = p & n = f & s = 0
        or self::node<_, r, n> * r::dsegP<s - 1, f, p, self>
	inv s >= 0;

dcl<s> == self = null & s = 0
        or self::node<_, r1, r2> * r2::dsegN<s - 1,self, self, r1>
	inv s >= 0;

//lemma "coer1" self::dsegN<p, n, t> <-> t::dsegP<self, p, n>;

lemma "coer2" self::dsegN<s, p, n, t> & s > 0 
	<-> self::dsegN<s - 1, p, t, r> * t::node<_, r, n>;

/* merging */
void prove1(node x)
	requires x::dsegN<s, p, t, r> * t::node<_, r, n>
	ensures x::dsegN<s1, p, n, t> & s1 = s + 1 & s1 > 0;
{
	unfold x';
}


/* breaking */
void prove(node x)
	requires x::dsegN<s, p, n, t> & s > 0
	ensures x::dsegN<s - 1, p, t, r> * t::node<_, r, n>;
{
	unfold x';
}


// delete circular

void delete_cir(ref node x, int s)
	requires x::dcl<s> & x != null
	ensures x'::dcl<s - 1>;
//	ensures x'::dcl<s1> & (s1=0 | s1=s-1);
{
//	if (x.next == x) {
	if (s == 1) {
		x = null;
		return;
	}
	else {
		node tmp = x.prev;
//dprint line10;
		tmp.next = x.next;
//		x.next.prev = x.prev;
		x = x.next;
dprint error;
		return;
/*
		if (x.next == x) { // for debugging only
//			dprint graph;
//assume false;
			return;
		}
		else {
dprint line13;
//debug on;
			return;
//debug off;
		}
*/
	}
}


void delete_cir1(ref node x, int s)
	requires x::dcl<s> & s >= 1
	ensures x'::dcl<s-1>;
{
	if (s == 1) {
		x = null;
	}
	else {
		x.prev.next = x.next;
		x.next.prev = x.prev;
		x = x.next;
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

void test3(node x)
	requires x::dsegN<s, p, n, t> & s > 0
	ensures true;
{
	node tmp = x.next;
	unfold tmp';
	dprint graph;
}