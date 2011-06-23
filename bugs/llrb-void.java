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
//              INSERTION               //
//////////////////////////////////////////


// Insert a value v to an INTERNAL node of a red-black tree.
// Remark: NO height increment.
node insert_internal(node h, int v)
	requires h::rbc<n,_,bh,c>
	case {
		c = 0 -> ensures res::node<v,0,null,null> & bh = 1 & n = 0; //res::rbc<1,0,1,4>;
		c = 1 -> //ensures res::rbc<n+1,1,bh,resc> & 1 <= resc <= 2;
				ensures res::rbc<n+1,1,bh,1> or res::rbc<n+1,1,bh,2>;
		c = 2 -> //ensures res::rbc<n+1,1,bh,resc> & 2 <= resc <= 3; 
				ensures res::rbc<n+1,1,bh,2> or res::rbc<n+1,1,bh,3>;
		c = 3 -> ensures res::rbc<n+1,0,bh,4>;
		(c < 0 | c >= 4) -> ensures res::rbc<n+1,0,bh,4> or res::rbs<n+1,bh>;
	}
{
	assume c != 3; // ONLY verified WITH --eps option
	//assume c = 3; // ONLY verified WITHOUT --eps option
	if (h == null) {
		return new node(v, 0, null, null); // RED node
	} else {
		if (rbcase(h) == 3) {
			h.color = 0;
			h.left.color = 1;
			h.right.color = 1;
		}

		if (v <= h.val) { // accept duplicates!
			h.left = insert_internal(h.left, v);
			// cannot detect that if h.left is of case 0 i.e. h.left = null 
			// then its bh = 1 & n = 1 at the beginning; lose this information
			// after the call and make the conclusion unreachable
			if (is_red(h.left)) {
				if (is_red(h.left.left)) {
					rotate_right(h);
//					node nr = new node(h.val, 0, h.left.right, h.right);
//					h.val = h.left.val;
//					h.left = h.left.left;
//					h.right = nr;
				}
			}
		} else {
			h.right = insert_internal(h.right, v);
			if (is_red(h.right)) {
				if (!is_red(h.left)) {
					rotate_left(h);
//					node nl = new node(h.val, 0, h.left, h.right.left);
//					h.val = h.right.val;
//					h.left = nl;
//					h.right = h.right.right;
				}
			}
		}

		return h;
	}
}


// Insert a value v to the ROOT node of a red-black tree
// Remark: POSSIBLE to have height increment.
node insert(node h, int v)
	requires h::rbc<n,_,bh,c>
	case {
		c = 0 -> ensures res::rbc<1,1,2,1>;
		c = 1 -> ensures res::rbc<n+1,1,bh,_>;
		c = 2 -> ensures res::rbc<n+1,1,bh,_>;
		(c < 0 | c >=3) -> ensures res::rbc<n+1,1,bh,_> or res::rbc<n+1,1,bh+1,_>;
	}
{
	h = insert_internal(h,v);
	if (is_red(h))
		h.color = 1;
	return h;
	dprint;
}


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

void rotate_left(node h)
	requires h::node<v,c,l,r> * r::node<rv,0,rl,rr>
	ensures h::node<rv,c,l1,rr> * l1::node<v,0,l,rl>;
{
	node nl = new node(h.val, 0, h.left, h.right.left);
	h.val = h.right.val;
	h.left = nl;
	h.right = h.right.right;
	dprint;
}

void rotate_right(node h)
	requires h::node<v,c,l,r> * l::node<lv,0,ll,lr>
	ensures h::node<lv,c,ll,r1> * r1::node<v,0,lr,r>;
{
	node nr = new node(h.val, 0, h.left.right, h.right);
	h.val = h.left.val;
	h.left = h.left.left;
	h.right = nr;
	dprint;
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
}
