/*
  ip routing
*/

data Route {
	// links
	Route left;
	Route right;
	Route mid;
	int depth;

	// address range
	int start;
	int end;
}

data Fs {
	Route queue;
}

/* tree of address ranges */

// depth, start address, end address
adtree<d, sa, ea> == self = null & d = 0 & sa = ea = 0
	or self::Route<left = l, right = r, mid = m, depth = d, start = sa, end = ea>
		* l::adtree<ld, lsa, lea> * r::adtree<rd, rsa, rea> * m::adtree<md, msa, mea>
		& lsa <= lea < sa <= ea < rsa <= rea
		& sa <= msa <= mea <= ea
		& d >= 0 // ignore depth constraint for now
//		& -1 <= ld - rd, ld - md, rd - md <= 1
//		& tmp1 = max(ld, rd) & tmp2 = max(tmp1, md) & d = tmp2 + 1 // this constraint is not possible here
	inv d >= 0;

freelist<n> == self = null & n = 0
	or self::Route<left = null, right = null, mid = m> * m::freelist<n - 1>
	inv n >= 0;

queue<n> == self = null & n = 0
	or self::Route<left = l, right = null, mid = m>
		* l::Route<> * m::queue<n - 1>
	inv n >= 0;

fs<n> == self::Fs<queue = q> * q::queue<n>;


void addnode(Fs f, ref Route cur, Route newroute, ref Route freelist)
	requires f::fs<fn> * cur::adtree<> * newroute::Route<> * freelist::freelist<nfree>
	ensures true;
{
dprint disj_count;
	if (cur == null) {
		cur = newroute;
		newroute.depth = 1;
		return;
	}

dprint disj_count;

	int cmp = rangecompare(newroute, cur);

dprint disj_count;

//dprint graph_keep;

	if (cmp == 1) { //case Rpreceeds:
		bind cur to (cleft, cright, cmid, cdepth, cs, ce) in {
			addnode(f, cleft, newroute, freelist);
		}
	}
	else if (cmp == 2) { // case Rfollows:
		bind cur to (cleft, cright, cmid, cdepth, cs, ce) in {
			addnode(f, cright, newroute, freelist);
		}
	}
	else if (cmp == 4) { //case Rcontains:
		/*
		 *  if newroute node is superset
		 *  of tree node,
		 *  replace tree node and
		 *  queue tree node to be
		 *  merged into root.
		 */
		Route p = cur;
		cur = newroute;
		newroute.depth = 1;
		bind f to (fqueue) in {
			addqueue(fqueue, p, freelist);
		}
dprint disj_count;
	}
	else if (cmp == 3) { //case Requals:
		/*
		 *  supercede the old entry if the old one isn't
		 *  a local interface.
		 */
		freeroute(newroute, freelist);
dprint disj_count;
	}
	else if (cmp == 5) { //case Rcontained:
		bind cur to (cleft, cright, cmid, cdepth, cs, ce) in {
			addnode(f, cmid, newroute, freelist);
		}
dprint disj_count;
	}

dprint disj_count;
	
	cur = balancetree(cur);
dprint disj_count;
}


Route balancetree(Route cur)
{
	Route l, r;
	int dl, dr;

	/*
	 * if left and right are
	 * too out of balance,
	 * rotate tree node
	 */

	dl = 0; 
	l = cur.left;
	if (l != null) dl = l.depth;

	dr = 0; 
	r = cur.right;
	if (r != null) dr = r.depth;

dprint disj_count;

	if (dl > dr + 1) {
		cur.left = l.right;
		l.right = cur;
		cur = l;
		calcd(cur);
		calcd(l);
	} 
	else if (dr > dl + 1) {
		cur.right = r.left;
		r.left = cur;
		cur = r;
		calcd(cur);
		calcd(r);
	} 
	else {
		calcd(cur);
	}

	return cur;
}

void calcd(Route p)
{
	Route q;
	int d;

	if (p != null) {
		d = 0;

		q = p.left;
		if (q != null)
			d = q.depth;

		q = p.right;
		if (q != null && q.depth > d)
			d = q.depth;

		q = p.mid;

dprint disj_count;

		if (q != null && q.depth > d)
			d = q.depth;

		p.depth = d + 1;
	}
}

int rangecompare(Route a, Route b)
{
	if (a.end < b.start)
		return 1; // a preceeds b

	if (a.start > b.end)
		return 2; // a follows b

	if (a.start <= b.start && a.end >= b.end) {
		if (a.start == b.end && a.end == b.end)
			return 3; // a and b are equal
		return 4; // a contains b
	}

	return 5; // a is contained in b
}


void addqueue(ref Route q, Route r, ref Route freelist)
	requires q::queue<n> * r::Route<> * freelist::freelist<fn>
		or q::queue<n> * freelist::freelist<fn> & r = null
	ensures q::queue<n1> * freelist'::freelist<fn1>
		& (fn1 = fn - 1 & fn > 0 & r != null 
			| fn1 = 0 & fn = 0 & r != null
			| fn1 = fn & r = null)
		& n1 >= n;
//		& (n1 = n & r = null | n1 = n + 1 & r != null);
{
	Route l;

	if (r == null) {
		return;
	}

	l = allocroute(freelist);
	l.mid = q;
	q = l;
	l.left = r;
}


void freeroute(Route r, ref Route freelist)
	requires r::Route<> * freelist::freelist<n>
	ensures freelist'::freelist<n+1>;
{
	r.left = null;
	r.right = null;
	r.mid = freelist;
	freelist = r;
}

Route allocroute(ref Route freelist)
	requires freelist::freelist<n>
	ensures res::Route<left = null, right = null, mid = null, depth = 0>
			* freelist'::freelist<m> & (m = n - 1 & n > 0 | m = 0 & n = 0);
{
	Route r;

	r = freelist;

	if (r != null) {
		freelist = r.mid;
	}
	else {
		r = new Route(null, null, null, 0, 0, 0);
	}

	r.mid = null;
	r.left = null;
	r.right = null;
	r.depth = 0;
	r.start = 0;
	r.end = 0;
	
	return r;
}

/*
void f(RouteTree t)
	requires t::RouteTree<right = r, mid =m, left = null>
	ensures t::RouteTree<>;
{
}
*/