/* 2-3 trees */
data node3 {
	int type;
	int maxl;	// max left, -1 for nothing
	int maxm;	// max middle, -1 for nothing	
	node3 left;
	node3 middle;
	node3 right;
	node3 parent;
}

tree2_3<h, n, p> == self = null & h = 0 & n = 0
	or self::node3<3, ml, mm, l, m, r, p> * l::tree2_3<hl, nl, pl> * m::tree2_3<hm, nm, pm> * r::tree2_3<hr, nr, pr> //3-node
	& pl = self & pm = self & pr = self
	& hl = hm & hl = hr & h = hl + 1 & n=nl+nm+nr+2
	or self::node3<2, ml, _, l, m, r, p> * l::tree2_3<hl, nl, pl> * m::tree2_3<hm, nm, pm> //2-node
	& pl = self & pm = self
	& r = null & hl = hm & h = hl + 1 & n=nl+nm+1
	inv n >= 0 & h>=0;

node3 search(node3 x, int k) //k>0
	requires x::tree2_3<_, _, _>
	ensures res::node3<_, k, _, _, _, _, _> or res::node3<_, _, k, _, _, _, _> or res=null;
{
	if (x != null) {
		if (k < x.maxl)
			return search(x.left, k);
		else if (k == x.maxl)
			return x;
		else if (k > x.maxl && k < x.maxm)
			return search(x.middle, k);
		else if (k == x.maxm)
			return x;
		else
			return search(x.right, k);
		
	} else
		return null;
}

node3 split_node(node3 x, int a, node3 c11, node3 c12, node3 c21, node3 c22)
	requires x::tree2_3<_, n, _> & x!=null
	ensures res::tree2_3<_, n+1, _>;
{
	node3 p, x1, x2;
	int up_val;

	if (x.parent == null)					// x is root
		p = new node3(-1, -1, null, null, null, null);
	else
		p = x.parent;

	x1 = new node3(-1, -1, c11, c12, null, p);
	x2 = new node3(-1, -1, c21, c22, null, p);

	if (a < x.maxl) {
		x1.maxl = a;
		x2.maxl = x.maxm;
		up_val = x.maxl;
	}
	else if (a > x.maxm) {
		x2.maxl = a;
		x1.maxl = x.maxl;
		up_val = x.maxm;
	} else {
		x1.maxl = x.maxl;
		x2.maxl = x.maxm;
		up_val = a;
	}

		
	//split_nodeting x into x1 and x2
	if (x.parent == null) {					// p is a new root
		p.maxl = up_val;
		p.left = x1;
		p.middle = x2;
		return p;
	} else {
		if (x.parent.type == 2) {				// p is a 2-node
			if (up_val < p.maxl) {
				p.maxm = p.maxl;
				p.maxl = up_val;
			} else
				p.maxm = up_val;

			if (p.left == x) {
				p.right = p.middle;
				p.left = x1;
				p.middle = x2;
			}

			if (p.middle == x) {
				p.middle = x1;
				p.right = x2;
			}
		
			return p;
		}
		else {						// p is a 3-node
			if (x.parent.left == x)
				return split_node(p, up_val, x1, x2, p.middle, p.right);
			else if (p.middle == x)	
				return split_node(p, up_val, p.left, x1, x2, p.right);
			else
				return split_node(p, up_val, p.left, p.middle, x1, x2);
		}
	}
}


/*
node3 insert(ref node3 x, int a) 
	requires x::tree2_3<h, n, _> & a >= 0
	ensures res::tree2_3<h1, n+1, _> & (h1=h | h1=h+1);
{
	node3 leaf = new node3(a, -1, null, null, null, null);	// creating a new leaf node
	node3 n = null;
	if (x == null) {					// x is empty
		return leaf;
	} else if (x.left == null) {				// x is a leaf
		if (x.maxm == -1) {				// x is a 2-node leaf
			if (a < x.maxl) {
				x.maxm = x.maxl;
				x.maxl = a;
			} else
				x.maxm = a;
			return x;
		} else {					// x is a 3-node leaf
			return split_node(x, a, n, n, n, n);
		}
	} else {						// x is an internal node
		if (a < x.maxl) {
			insert(x.left, a);
		} else if (a > x.maxm) {
			insert(x.right, a);
		} else {
			insert(x.middle, a);
		}
		return x;
	}
}
*/



