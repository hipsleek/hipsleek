data itvl {
	int low;
	int high;
	itvl next;
}

data tnode {
	int ctr; // center point -- computed as the the midpoint of the first interval added to 'items'
	itvl items; // all intervals containing the center point
	tnode left; // all intervals to the left
	tnode right; // all intervals to the right
}

/*
	List of intervals stored at each node of the tree.
	All intervals in the list must contain ctr.
*/
ilist<ctr @ in, lo, hi> == self::itvl<lo, hi, null> & lo <= ctr <= hi
	or self::itvl<low, high, r> * r::ilist<ctr, rlo, rhi> 
		& lo = min(low, rlo) & hi = max(high, rhi) & low <= ctr <= high
	inv lo <= ctr <= hi;

ilist1<ctr>  == self = null
	or self::itvl<low, high, r> * r::ilist1<ctr> & low <= ctr <= high;

lemma self::ilist<ctr, lo, hi> -> self::ilist1<ctr>;

/*
	Interval tree.
	l, r are leftmost and rightmost point of all intervals in the tree.
*/
itree<ctr, lm, rm> == self = null & lm <= ctr <= rm
	or self::tnode<ctr, it, l, r> * l::itree<lctr, llm, lrm> 
		* r::itree<rctr, rlm, rrm> * it::ilist<ctr, lo, hi> 
		& lctr <= ctr <= rctr
		& lrm <= ctr <= rlm 
		& lm = min(llm, lo) & rm = max(rrm, hi)
	inv lm <= ctr <= rm;

void delete(ref tnode t, int lo, int hi)
	requires t::itree<ctr, lm, rm> & t != null
	ensures t'::itree<rctr, rlm, rrm> & lm <= rlm <= rrm <= rm;
{		
	if (lo <= t.ctr && t.ctr <= hi) {
		bind t to (tctr, titems, tleft, tright) in {
			delete_list(titems, lo, hi);
			if (titems == null) {
				if (tleft == null) {
					t = tright;
				}
				else if (tright == null) {
					t = tleft;
				}
				else {
					tnode tmp = delete_left_max1(tleft);
					tctr = tmp.ctr;
					titems = tmp.items;
				}
			}
		}
		return;
	}
	else if (hi < t.ctr) {
		bind t to (_, _, tleft, _) in {
			if (tleft != null)
				delete(tleft, lo, hi);
		}
		return;
	}
	else {
		bind t to (_, _, _, tright) in {
			if (tright != null)
				delete(tright, lo, hi);
		}
		return;
	}
}

tnode delete_left_max1(ref tnode t)
	requires t::itree<ctr, lm, rm> & t != null
	ensures t'::itree<ctr1, lm1, rm1> 
			* res::tnode<rctr, ritems, _, _> 
			* ritems::ilist<rctr, rlo, rhi>
			& lm <= lm1 <= rm1 <= rm & rm1 <= rctr <= rm & lm <= rlo <= rhi <= rm;
{
	if (t.right == null) {
		tnode tmp = t;
		t = t.left;
		return tmp;
	}
	else {
		tnode tmp;
		bind t to (_, _, _, tright) in {
			tmp = delete_left_max1(tright);
		}

		if (get_lo(tmp.items) < get_hi(t.items)) {
			itvl tmp1 = tmp.items;
			tmp.items = t.items;
			t.items = tmp1;

			int tmp3 = tmp.ctr;
			tmp.ctr = t.ctr;
			t.ctr = tmp3;
			return tmp;
		}
		else {
			return tmp;
		}
	}
}

int get_lo(itvl items)
	requires items::ilist<ctr, lo, hi>
	ensures items::ilist<ctr, lo, hi> & res = lo;

int get_hi(itvl items)
	requires items::ilist<ctr, lo, hi>
	ensures items::ilist<ctr, lo, hi> & res = hi;

void delete_list(ref itvl items, int lo, int hi)
	requires items::ilist<ctr, low, high>
	ensures items'::ilist<ctr, rlow, rhigh> & low <= rlow <= rhigh <= high
			or items' = null;
{
	if (items != null) {
		if (items.low == lo && items.high == hi) {
			items = items.next;
		}
		else {
			bind items to (il, ih, inext) in {
				if (inext != null)
					delete_list(inext, lo, hi);
			}
		}
	}
}

tnode insert_itvl(tnode t, int lo, int hi)	
	requires t::itree<ctr, lm, rm> & lo <= hi 
	ensures res::itree<rctr, rlm, rrm> & rlm = min(lm, lo) & rrm = max(rm, hi);
{
	tnode tmp;
	int ctr = lo; //div2(lo, hi);

	if (t == null) {
		itvl ltmp = new itvl(lo, hi, null);
		tmp = new tnode(ctr, ltmp, null, null);
		return tmp;
	}

	// if [lo, hi] contains the root's center, add it there
	if (lo <= t.ctr && t.ctr <= hi) {
		itvl ltmp = new itvl(lo, hi, t.items);	
		t.items = ltmp;
		return t;
	}
	else if (hi < t.ctr) {
		t.left = insert_itvl(t.left, lo, hi);
	}
	else {
		t.right = insert_itvl(t.right, lo, hi);
	}

	return t;
}


/* search for intervals containing p */
itvl search_list(itvl l, int p)
	requires l::ilist<ctr, lo, hi> 
	ensures res::ilist1<p>;
{
	if (l == null) return null;

	itvl tmp1;
	if (l.next != null) 
		tmp1 = search_list(l.next, p);
	else
		tmp1 = null;
	
	if (l.low <= p && p <= l.high) {
		tmp1 = new itvl(l.low, l.high, tmp1);
	}
		
	return tmp1;
}

itvl append(itvl x, itvl y)
	requires x::ilist1<ctr> * y::ilist1<ctr>
	ensures res::ilist1<ctr>;
{
	if (x == null) {
		return y;
	}
	else if (x.next == null) {
		x.next = y;
		return x;
	}
	else {
		x.next = append(x.next, y);
		return x;
	}
}

itvl point_query(tnode t, int p)
	requires t::itree<ctr, lm, rm> 
	ensures res::ilist1<p>;
{
	if (t == null) 
		return null;

	if (p == t.ctr) 
		return t.items;
	
	itvl tmp1 = search_list(t.items, p);
	itvl tmp2;

	if (p < t.ctr) {
		tmp2 = point_query(t.left, p);
	}
	else {
		tmp2 = point_query(t.right, p);
	}

	itvl tmp3 = append(tmp1, tmp2);
	return tmp3;
}

itvl test(itvl x, int lo, int hi)
	requires x::ilist<ctr, a, b> & lo <= ctr <= hi
	ensures res::ilist<_,_,_>;
{
	itvl tmp = new itvl(lo, hi, x);
	
	return tmp;
}

int div2(int a, int b)
	requires true ensures a <= res <= b;
