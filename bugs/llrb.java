/*
 Left-leaning Red Black Tree
 Modified from RedBlackBST.java
 @author: Vu An Hoa
 */

data node {
	int val;
	int color; // 0 for red, 1 for black
	node left;
	node right;
}

// Red black tree with case analysis
// Remark: color information is already known in the case!
rbc<n, cl, bh, c> == 
	// BASE CASE
	self = null & n = 0 & bh = 1 & cl = 1 & c = 0
	// c = 1:   B
	//        B   B
	or self::node<v, 1, l, r> * l::rbc<ln, 1, bh - 1, _> * r::rbc<rn, 1, bh - 1, _> & cl = 1 & n = 1 + ln + rn & c = 1
	// c = 2:   B
	//        R   B
    or self::node<v, 1, l, r> * l::rbc<ln, 0, bh - 1, 4> * r::rbc<rn, 1, bh - 1, _> & cl = 1 & n = 1 + ln + rn & c = 2
	// c = 3:   B
	//        R   R
    or self::node<v, 1, l, r> * l::rbc<ln, 0, bh - 1, 4> * r::rbc<rn, 0, bh - 1, 4> & cl = 1 & n = 1 + ln + rn & c = 3
	// c = 4:   R
	//        B   B
	or self::node<v, 0, l, r> * l::rbc<ln, 1, bh, _> * r::rbc<rn, 1, bh, _> & cl = 0 & n = 1 + ln + rn & c = 4
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1 & 0 <= c <= 4;

// Special case         R   
//                    R   B
rbs<n, bh> == 
	self::node<_,0,l,r> * l::rbc<ln,0,bh,4> * r::rbc<rn,1,bh,_> & ln + rn + 1 = n
	inv n >= 1 & bh >= 1 & self!=null;

//////////////////////////////////////////
//          HELPER FUNCTIONS            //
//////////////////////////////////////////
// Specification node naming convention:
// h : main node
// lt : left tree; rt : right tree
// llt : lt's left tree; rlt : rt's left tree; ...


// Identify the case of the red black tree rooted at h
// as in the definition.
int rbcase(node h)
	requires h::rbc<n,cl,bh,c>@I
	ensures res = c;
{
	if (h == null)
		return 0;
	else {
//		dprint;
		if (h.color == 0)
			return 4;
		else {
			assert cl = 1;
			dprint;
			if (is_red(h.left)) {
				if (is_red(h.right))
					return 3;
				else
					return 2;
			} else
				return 1;
		}
	}
//	dprint;
}

int rbsize(node h)
	requires h::rbc<n,cl,bh,c>@I
	ensures res = n;
{
	if (h == null)
		return 0;
	else {
		int ls = rbsize(h.left);
		int rs = rbsize(h.right);
		int r = 1 + ls + rs;
		dprint;
		return 1 + ls + rs;
	}
}

// Check if h is a red node or not.
bool is_red(node h)
	case{
		h  = null -> ensures !res;
		h != null -> requires h::node<v,c,l,r>@I 
//						ensures h::node<v,c,l,r> & c != 0 & !res 
//        				or h::node<v,c,l,r> & c = 0 & res;
		/** Replace a single ensure by case analysis **/
		case {
			c = 0 -> ensures res;
			c != 0 -> ensures !res;
		}
	}
{
	dprint;
	if (h == null)
		return false;
	else {
		return (h.color == 0);
		/** Replaced by expanded code **/
//		if (h.color == 0)
//			return true;
//		else
//			return false;
	}
	dprint;
}

// Flip the color of a node and its two children.
void color_flip(node h)
	requires h::node<v,c,l,r> * l::node<lv,lc,ll,lr> * r::node<rv,rc,rl,rr>
	ensures h::node<v,1-c,l,r> * l::node<lv,1-lc,ll,lr> * r::node<rv,1-rc,rl,rr>;
{
	assert h != null;
	h.color        = 1 - h.color;
	dprint;
	h.left.color   = 1 - h.left.color;
	dprint;
	h.right.color  = 1 - h.right.color;
	dprint;
}

// Make a right-leaning 3-node lean to the left.
node rotate_left(node h)
//	requires h::node<v,c,l,r> * r::node<rv,0,rl,rr>
//	ensures res::node<rv,c,h,rr> * h::node<v,0,l,rl> & res = r;
	requires h::node<_,1,l,r> * l::rbc<ln,1,bh,_> * r::rbc<rn,0,bh,4>
	ensures res::rbc<1+ln+rn,1,bh+1,2>;
{
	node nl = new node(h.val, 0, h.left, h.right.left);
	h.val = h.right.val;
	h.left = nl;
	h.right = h.right.right;
	return h;
	
//	node x = h.right;
//	h.right = x.left;
//	x.left = h;
//	x.color = x.left.color;
//	x.left.color = 0;
//	return x;
}

// Make a left-leaning 3-node lean to the right.
node rotate_right(node h)
	requires h::node<v,c,l,r> * l::node<lv,0,ll,lr>
	ensures res::node<lv,c,ll,h> * h::node<v,0,lr,r> & res = l;
//	requires h::node<_,1,l,r> * l::rbc<ln,0,bh,4> * r::rbc<rn,1,bh,_>
//	ensures res::node<_,1,l1,r1> * l1::rbc<ln1,1,bh,_> * r1::rbc<rn1,0,bh,4> & ln + rn = ln1 + rn1;
{
	node nr = new node(h.val, 0, h.left.right, h.right);
	h.val = h.left.val;
	h.left = h.left.left;
	h.right = nr;
	return h;
	
//	node x = h.left;
//	h.left = x.right;
//	x.right = h;
//	x.color = x.right.color;
//	x.right.color = 0;
//	return x;
}

// Compute the black height of a red black tree
int black_height(node h)
	requires h::rbc<_,_,bh,_>@I
	ensures res = bh;
{
	if (h == null)
		return 1;
	else
		return h.color + black_height(h.left);
	dprint;
//	if (is_red(h))
//		return black_height(h.left);
//	else
//		return 1 + black_height(h.left);
}

//Assuming that h is red and both h.left and h.left.left
//are black, make h.left or one of its children red.
node move_red_left(node h)
	requires h::node<_,0,l,r> * l::rbc<ln,1,bh,1> * r::rbc<rn,1,bh,c>
	case {
		c  = 1 -> ensures res::node<_,1,resl,resr> * 
						resl::rbc<ln,0,bh-1,4> * 
						resr::rbc<rn,0,bh-1,4>;
		c != 1 -> ensures res::node<_,0,resl,resr> * 
        				resl::rbc<resln,1,bh,2> * 
        				resr::rbc<resrn,1,bh,_> & 
        				resln + resrn = ln + rn;
	}
{
	color_flip(h);

	if (is_red(h.right.left)) {
		h.right = rotate_right(h.right);
		h = rotate_left(h);
		color_flip(h);
		
		// Ensure left-leaning on the right branch! 
		// Robert seemed not to notice this.
		if (!is_red(h.right.left))
			if (is_red(h.right.right))
				h.right = rotate_left(h.right);
	}

	dprint;
	
	return h;
}

//Assuming that h is red and both h.right and h.right.left
//are black, make h.right or one of its children red.
node move_red_right(node h)
	requires h::node<_,0,l,r> * l::rbc<ln,1,bh,c> * r::rbc<rn,1,bh,1>
	ensures res::rbc<n,1,bh,3>
     	or  res::node<_,0,resl,resr> * 
     		resl::rbc<resln,1,bh,_> * 
     		resr::rbc<resrn,1,bh,2> & 
     		resln + resrn = ln + rn
     	or 	res::node<_,0,resl,resr> * 
     		resl::rbc<resln,1,bh,_> * 
     		resr::rbc<resrn,1,bh,3> & 
     		resln + resrn = ln + rn;
{
	color_flip(h);
	
	if (is_red(h.left.left)) {
		h = rotate_right(h);
		color_flip(h);
		
		// Ensure left leaning for the tree on the right branch.
		if (!is_red(h.right.left))
			h.right = rotate_left(h.right);
	}
	
	return h;
}

//////////////////////////////////////////
//              INSERTION               //
//////////////////////////////////////////

// Insert a value v to the ROOT node of a red-black tree
// Remark: POSSIBLE to have height increment.
node insert(node h, int v)
	requires h::rbc<n,_,bh,c>
	//PROBLEM DETECTED: THIS POST-CONDITION CANNOT BE VERIFIED SIMPLY BECAUSE THE SYSTEM DOES NOT KNOW
	//THAT IT NEEDS TO PERFORM A CASE SWITCH ON c!
	//ensures res::rbc<n+1,1,bh,_> or res::rbc<n+1,1,bh+1,_>;
	case {
		c = 0 -> ensures res::rbc<1,1,2,1>;
		c = 1 -> ensures res::rbc<n+1,1,bh,_>;
		c = 2 -> ensures res::rbc<n+1,1,bh,_>;
		(c < 0 | c >=3) -> ensures res::rbc<n+1,1,bh,_> or res::rbc<n+1,1,bh+1,_>;
	}
{
	node r = insert_internal(h,v);
	dprint;

	if (is_red(r))
		r.color = 1;

	return r;
}

// Insert a value v to an INTERNAL node of a red-black tree.
// Remark: NO height increment.
node insert_internal(node h, int v)
	requires h::rbc<n,_,bh,c>
	case {
		c = 0 -> ensures res::node<v,0,null,null>; //res::rbc<1,0,1,4>;
		c = 1 -> //ensures res::rbc<n+1,1,bh,resc> & 1 <= resc <= 2;
				ensures res::rbc<n+1,1,bh,1> or res::rbc<n+1,1,bh,2>;
		c = 2 -> //ensures res::rbc<n+1,1,bh,resc> & 2 <= resc <= 3; 
				ensures res::rbc<n+1,1,bh,2> or res::rbc<n+1,1,bh,3>;
		c = 3 -> ensures res::rbc<n+1,0,bh,4>;
		(c < 0 | c >= 4) -> ensures res::rbc<n+1,0,bh,4> or res::rbs<n+1,bh>;
	}
{
	//assume (c < 0 | c >=4); // = 3;
	
	if (h == null)
		return new node(v, 0, null, null); // RED node
	
//	dprint;	

//	if (is_red(h.left))
//		if (is_red(h.right))
//			color_flip(h);
	/** Replace the equivalent code below **/
	if (rbcase(h) == 3) {
//		color_flip(h);
		h.color = 0;
		h.left.color = 1;
		h.right.color = 1;
	}
	/** End of replacement **/
	
	//dprint;
	// dprint implies the assertion is correct in case c = 3!
	// fail!
	//assert h'::rbc<_,_,_,_>; 
	
	//int a = h.val;
	//assume v <= a';
	
	if (v <= h.val) { // accept duplicates!
		h.left = insert_internal(h.left, v);
//		dprint;
		if (is_red(h.left)) {
//			assert false;
			if (is_red(h.left.left)) {
//				h = rotate_right(h);
				/** Expand to equivalent code below **/	
				node nr = new node(h.val, 0, h.left.right, h.right);
				h.val = h.left.val;
				h.left = h.left.left;
				h.right = nr;
//				node x = h.left;
//				h.left = x.right;
//				x.right = h;
//				x.color = x.right.color;
//				x.right.color = 0;
//				h = x;
				/** End of expansion **/
			}
		}
		// the state is correct!
//		dprint;
	} else {
//		assume false;
		h.right = insert_internal(h.right, v);
		if (is_red(h.right)) {
			if (!is_red(h.left)) {
//				h = rotate_left(h);
				/** Expand to equivalent code below **/	
				node nl = new node(h.val, 0, h.left, h.right.left);
				h.val = h.right.val;
				h.left = nl;
				h.right = h.right.right;
//				node x = h.right;
//				h.right = x.left;
//				x.left = h;
//				x.color = x.left.color;
//				x.left.color = 0;
//				h = x;
				/** End of expansion **/
			}
		}
	}
	dprint;
	// case c = 3 ==> folding error here!
//	assert h'::node<_,0,lx,rx> * lx::rbc<ln,1,bh,_> * rx::rbc<rn,1,bh,_> & ln + rn = n; 

	// case c = 4 ==> folding error + case analysis fail detected in sleek
//	assert h'::node<_,0,lx,rx> * lx::rbc<ln,_,bh,_> * rx::rbc<rn,1,bh,_> & ln + rn = n;

	return h;
}

void foo(node h)
	requires h::node<_,0,lx,rx> * lx::rbc<ln,1,bh,_> * rx::rbc<rn,1,bh,_>
	ensures h::rbc<ln+rn+1,0,bh,4>;
	requires h::node<_,1,lx,rx> * lx::rbc<ln,0,bh,_> * rx::rbc<rn,0,bh,_>
	ensures h::rbc<ln+rn+1,0,1+bh,3>;
	requires h::node<_,1,lx,rx> * lx::rbc<ln,0,bh,_> * rx::rbc<rn,1,bh,_>
	ensures h::rbc<ln+rn+1,0,1+bh,2>;
	requires h::node<_,1,lx,rx> * lx::rbc<ln,1,bh,_> * rx::rbc<rn,1,bh,_>
	ensures h::rbc<ln+rn+1,0,1+bh,1>;
	requires h=null
	ensures h::rbc<0,1,1,0>;
	requires h::node<_,0,l,r> * l::rbc<ln,0,bh,4> * r::rbc<rn,1,bh,_>
	ensures h::rbs<ln+rn+1,bh>;

//////////////////////////////////////////
//           DELETE MINIMUM             //
//////////////////////////////////////////

node delete_min(node h, ref int min_value)
	requires h::rbc<n,1,bh,_> & n >= 1
	ensures res::rbc<n-1,1,bh,_> or res::rbc<n-1,1,bh-1,_>;
{
	// NOTE: height change occurs here! At the root level,
	// convert     B        into     R
	//           B   B             B   B
	// to meet the pre-condition of delete_min_internal.
	if (!is_red(h.left)) h.color = 0;

	h = delete_min_internal(h, min_value);

	// Convert the RED root back to BLACK.
	if (is_red(h)) h.color = 1;

	return h;
}

// Delete the node with minimum value under h
// and return that minimum value.
// NOTE: NO CHANGE IN HEIGHT
node delete_min_internal(node h, ref int min_value)
	requires h::rbc<n,_,bh,c> & c >= 2 & n >= 1
	case { // 3.020187
		c = 2 -> //ensures res::rbc<n-1,1,bh,resc> & 1 <= resc <= 2; // 4.444277
				ensures res::rbc<n-1,1,bh,2> or res::rbc<n-1,1,bh,1>; // 2.42015
		c = 3 -> //ensures res::rbc<n-1,1,bh,resc> & 2 <= resc <= 3; // 5.244326
				ensures res::rbc<n-1,1,bh,3> or res::rbc<n-1,1,bh,2>; // 2.388148
		// the following case is actually just c = 4 as 2 <= c <= 4 is in the assumption
		(c < 2 | c >= 4) -> case {
			n = 1 -> ensures res::rbc<n-1,1,bh,0> & bh = 1; // 2.468153
			n != 1 -> //ensures res::rbc<n-1,1,bh,resc> & 3 <= resc <= 4;
				 ensures res::rbc<n-1,0,bh,4> or res::rbc<n-1,1,bh,3>;
		}
	}
{
	assume c = 4;
	assume n != 1;
	if (h.left == null) {
		min_value = h.val;
		return null;
	}
	dprint;
	
//	if (!is_red(h.left))
//		if (!is_red(h.left.left))
//			h = move_red_left(h);
	/** Expand to equivalent code below **/
	if (rbcase(h.left) == 1) {
//		color_flip(h);
		h.color = 1 - h.color;
		h.left.color = 1 - h.left.color;
		h.right.color = 1 - h.right.color;
		
		if (is_red(h.right.left)) {
//			h.right = rotate_right(h.right);
			node y = h.right.left;
			h.right.left = y.right;
			y.right = h.right;
			y.color = y.right.color;
			y.right.color = 0;
			h.right = y;
			
//			h = rotate_left(h);
			y = h.right;
			h.right = y.left;
			y.left = h;
			y.color = y.left.color;
			y.left.color = 0;
			h = y;
			
//			color_flip(h);
			h.color = 1 - h.color;
			h.left.color = 1 - h.left.color;
			h.right.color = 1 - h.right.color;
			
			// Ensure left-leaning on the right branch! 
			// Robert seemed not to notice this.
			if (!is_red(h.right.left)) {
				if (is_red(h.right.right)) {
//					h.right = rotate_left(h.right);
					node x = h.right.right;
					h.right.right = x.left;
					x.left = h.right;
					x.color = x.left.color;
					x.left.color = 0;
					h.right = x;
				}
			}
		}
	}
	/** End of expansion **/
	
	h.left = delete_min_internal(h.left, min_value);
	
	if (is_red(h.right)) {
		if (!is_red(h.left)) {
//			h = rotate_left(h);
			/** Expand to equivalent code below **/
			node x = h.right;
			h.right = x.left;
			x.left = h;
			x.color = x.left.color;
			x.left.color = 0;
			h = x;
			/** End of expansion **/
		}
	}
	

	
	return h;
}

//////////////////////////////////////////
//              DELETION                //
//////////////////////////////////////////

// Delete the value v in the red black tree if it appears.
node delete(node h, int v)
	requires h::rbc<n,1,bh,_> // root node is assumed to be always black
	ensures res::rbc<resn,1,resbh,_> & n-1 <= resn <= n & bh - 1 <= resbh <= bh;
{
	if (h != null) {
		// change 2 node into pseudo-4
		if (!is_red(h.left)) h.color = 0;
		
		h = delete_internal(h, v);
		
		// restore the color of the root node
		if (is_red(h)) h.color = 1;
	}
	
	return h;
}

// Delete without changing the height
node delete_internal(node h, int v)
	requires h::rbc<n,_,bh,c> & c >= 2
	case {
		c = 2 -> ensures res::rbc<n1,_,bh,2> & n-1 <= n1 <= n 
						or res::rbc<n1,_,bh,1> & n-1 <= n1 <= n;
		c = 3 -> ensures res::rbc<n1,_,bh,3> & n-1 <= n1 <= n 
						or res::rbc<n1,_,bh,2> & n-1 <= n1 <= n;
		(c < 2 | c >= 4) -> ensures res::rbc<n1,0,bh,4> & n-1 <= n1 <= n
						or res::rbc<n1,1,bh,3> & n-1 <= n1 <= n 
		 				or res::rbc<n1,1,bh,0> & n-1 <= n1 <= n;
	}
{	
	if (v < h.val) {
		if (h.left != null) {
			if (!is_red(h.left) && !is_red(h.left.left))
				h = move_red_left(h);
			
			h.left = delete_internal(h.left, v);
			
			//fix_up(h); 
			// what could possibly go wrong? only the left-leaning property!
			if (is_red(h.right) && !is_red(h.left))
				h = rotate_left(h);
		}
	} else {
		if (v >= h.val) { // v >= h.val		
			if (is_red(h.left))
				h = rotate_right(h);
	
			if (v == h.val && (h.right == null))
				h = null;
			
			if (!is_red(h.right) && !is_red(h.right.left))
				h = move_red_right(h); 
			
			if (v == h.val) {
				int m;
				h.right = delete_min(h.right, m);
				h.right.val = m;
			}
			else 
				h.right = delete_internal(h.right, v);
			
			//fix_up(h); // what can go wrong?
			if (is_red(h.right) && !is_red(h.left))
				h = rotate_left(h);
		}
	
	}

	return h;
}
