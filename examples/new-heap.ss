data node {
	int val;
	bool complete;
	node left;
	node right;
}



/*
bh<c,h,mx> == self=null & c & mx=0 & h=0
	or self::node<v,c,l,r> * l::bh<lc,lh,lx> * r::bh<rc,rh,rx>
		& mx=v>=lx,rx
		& h=lh+1 & (lc & rc & c & lh=rh | lc & rc & !c & lh=rh+1
					| !lc & rc & !c & lh=rh+1 | lc & !rc & !c & lh=rh & lh>0)
	inv  h>=0 & mx>=0;
*/
//		& (lc & rc & c & lh=rh & h=lh+1 | lc & rc & !c & lh=rh+1 & h=lh+1 
//			| !lc & rc & !c & h=lh+1 & lh=rh+1 | lc & !rc & !c & h=lh+1 & lh=rh)


bh<c,h> == self=null & c & h=0
	or self::node<v,c,l,r> * l::bh<lc,lh> * r::bh<rc,rh>
		& h=lh+1 & (lc & rc & c & lh=rh | lc & rc & !c & lh=rh+1
					| !lc & rc & !c & lh=rh+1 | lc & !rc & !c & lh=rh & lh>0)
	inv  h>=0;



int read_int() {
	int i1 = -1;
	java {
		try {
			java.io.InputStreamReader stdin =
					new java.io.InputStreamReader(System.in);
			java.io.BufferedReader console =
					new java.io.BufferedReader(stdin);

			java.lang.String s1 = console.readLine();
			i1 = Integer.parseInt(s1);
		}
		catch (Exception e) {}
	}
	return i1;
}

/*
node test()
	requires true
	ensures res::bh<f, h, mx>;
{
	node tmp1 = new node(10, true, null, null);

	node tmp2 = new node(15, true, null, null);

	assert tmp2'::bh<a,1,15> & a;

	node tmp = new node(20, false, tmp1, null);

	tmp.right = tmp2;
	tmp.complete = true;

	return tmp;
}
*/

node insert(node t, int v) 
	requires t::bh<c,h> & v>=0
	ensures res::bh<rc,rh> & (c & rh=h+1 & !rc | !c & rh=h) & t!=null
			or res::bh<rc,1> & rc & t=null;
{
	if (t==null) {
		return new node(v, true, null, null);
	}
	else {
		int smallest; // this is the element to be pushed down
		if (t.val < v) {
			t.val = v; // v stays here, t.val will be pushed down
			smallest = t.val;
		}
		else smallest = v; // v is pushed down

		if (t.left == null) {
			// assert t'::node<tv,tc,tl,tr> & tr=null & tl=null;
			t.left = new node(smallest, true, null, null);
			t.complete = false; // t is no longer complete
			return t;
		}
		else if (t.right == null) { // the left must be a tree with a single node
			node tmp = new node(smallest, true, null, null);
			t.right = tmp;
			t.complete = true; // t is now complete
/*
			assert t'::node<tv,tc,tl,tr> * tl::node<tlv, tlc, tll, tlr>
					* tr::node<trv, trc, trl, trr>
				& tc & tv>=tlv,trv
				& tll,tlr=null & tlc
				& trl,trr=null & trc;

			assert t'::node<tv,tc,tl,tr> * tl::bh<tlc,tlh,tlx> * tr::bh<trc,trh,trx>
				& tlh=1 & tlc;
*/
			return t;
		}
		else if (!t.left.complete) {
			// insert to left child
			t.left = insert(t.left, smallest);
			return t;
		}
		else if (t.left.complete && t.right.complete) {
			// insert to left child
			t.left = insert(t.left, smallest);

			assume false;

			return t;

		}
		else {
			// insert to right for the only remaining case:
			// left is complete, but right is not

//			assert t'::node<tv, tc, tl, tr> * tl::bh<tlc,tlh> * tr::bh<trc,trh>
//				& tlc & !trc & trh<=tlh<=trh+1;
	
			node tmp2 = insert(t.right, smallest);

//			assert tmp2'::bh<_,_>;

			t.right = tmp2;
			// what to do with t.c ???
			// counterexample explanation: how to point out that t.complete is the trouble?

			assert t'::bh<th, tc>;

			return t;
		}
	}
}

void print_tree(node t, int n) {
java {
	if (t == null) return;
	
	for (int i = 0; i < n; i++) System.out.print(" ");
	System.out.println(t.val);
	print_tree(t.left, n+2);
	print_tree(t.right, n+2);
}
}

void main() {
//	node t = test();
//	print_tree(t, 1);
}
