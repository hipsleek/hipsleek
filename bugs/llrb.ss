/**
 Left-leaning Red Black Tree
 Modified from RedBlackBST.java
 @author: Vu An Hoa
 */

data node {
	int val;
	int color; /* 0 for red, 1 for black */
	node left;
	node right;
}

/* view for red-black trees */
rb<n, cl, bh> == self = null & n = 0 & bh = 1 & cl = 1
	// self is red, both child must be black
	or self::node<v, 0, l, r> * l::rb<ln, 1, lbh> * r::rb<rn, 1, rbh>
	   & cl = 0 & n = 1 + ln + rn & lbh = bh & rbh = bh
	// if left is black, right must be black due to left-leaning!
	or self::node<v, 1, l, r> * l::rb<ln, 1, lbh> * r::rb<rn, 1, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh
	or self::node<v, 1, l, r> * l::rb<ln, 0, lbh> * r::rb<rn, _, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;


//////////////////////////////////////////
//          HELPER FUNCTIONS I          //
//////////////////////////////////////////
// Specification node naming convention:
// h : main node
// lt : left tree; rt : right tree
// llt : lt's left tree; rlt : rt's left tree; ...


bool is_red(node h)
	case{
		h  = null -> requires true 
		             ensures !res;
		h != null -> requires h::node<v,c,l,r>
		             ensures h::node<v,c,l,r> & c != 0 & !res 
		                     or h::node<v,c,l,r> & c = 0 & res;
	}
{
	if (h==null)
		return false;
	else
		return (h.color==0);
}

void color_flip(node h)
	requires h::node<v,c,l,r> * l::node<lv,lc,ll,lr> * r::node<rv,rc,rl,rr>
	ensures h::node<v,1-c,l,r> * l::node<lv,1-lc,ll,lr> * r::node<rv,1-rc,rl,rr>;
{
	h.color        = 1 - h.color;
	h.left.color   = 1 - h.left.color;
	h.right.color  = 1 - h.right.color;
}

// Make a right-leaning 3-node lean to the left.
node rotate_left(node h)
	requires h::node<v,c,l,r> * r::node<rv,0,rl,rr>
	ensures res::node<rv,c,l1,rr> * l1::node<v,0,l,rl>;
{
	node x = h.right;
	h.right = x.left;
	x.left = h;
	x.color = x.left.color;
	x.left.color = 0;
	return x;
}

// Make a left-leaning 3-node lean to the right.
node rotate_right(node h)
	requires h::node<v,c,l,r> * l::node<lv,0,ll,lr>
	ensures res::node<lv,c,ll,r1> * r1::node<v,0,lr,r>;
{
	node x = h.left;
	h.left = x.right;
	x.right = h;
	x.color = x.right.color;
	x.right.color = 0;
	return x;
}

//////////////////////////////////////////
//              INSERTION               //
//////////////////////////////////////////

node insert(node h, int v)
	requires h::rb<n,_,bh>
	ensures res::rb<n+1,_,_>;
{
	if (h == null) { // leaf
		return new node(v, 0, null, null);
	}

	// split this node if it is a 4 node
	if (h.left != null && h.right != null) { 
		if (is_red(h.left) && is_red(h.right)) {
			color_flip(h);
			assert h'::rb<n,_,_>;
		}
	}
	assert h'::rb<n,_,_>;
	
	if (v <= h.val) // accept duplicates!
		h.left = insert(h.left, v);
	else
		h.right = insert(h.right, v);
	
	if (h.right != null)
		if (is_red(h.right))
			h = rotate_left(h);
	
	if (h.left != null)
		if (h.left.left != null)
			if (is_red(h.left) && is_red(h.left.left))
				h = rotate_right(h);
	
	return h;
}

//////////////////////////////////////////
//         HELPER FUNCTIONS II          //
//////////////////////////////////////////

// Assuming that h is red and both h.left and h.left.left
// are black, make h.left or one of its children red.
void move_red_left(node h)	
	requires h::node<v,0,lt,rt> * lt::node<lv,1,llt,lrt> 
	  * rt::node<rv,rc,rlt,rrt> * llt::node<llv,1,lllt,llrt> 
	  * rlt::node<rlv,rlc,rllt,rlrt> * rlrt::node<rlrv,rlrc,rlrlt,rlrrt>
	case {
		rlc = 0
		-> ensures h::node<v,0,lt,rlrt> * lt::node<lv,1,llt,lrt> 
			* llt::node<llv,1,lllt,llrt> * rt::node<rv,1-rlrc,rlrt,rrt> 
			* rlt::node<rlv,0,rllt,rlrt> * rlrt::node<rlrv,0,rlrlt,rlrrt>;
	    rlc != 0
	    -> ensures h::node<v,1,lt,rt> * lt::node<lv,0,llt,lrt> 
	       * rt::node<rv,1-rc,rlt,rrt> * llt::node<llv,1,lllt,llrt> 
	       * rlt::node<rlv,rlc,rllt,rlrt> * rlrt::node<rlrv,rlrc,rlrlt,rlrrt>; //after color_flip
	}
{
	color_flip(h);
	if (is_red(h.right.left)) {		
		rotate_right(h.right);
		rotate_left(h);		
		color_flip(h);
	}
}

// Fix the invariant
node fix_up(node h)
	requires h::node<v,c,lt,rt> * lt::rb<ln,lc,lh> * rt::rb<rn,rc,rh> & lh = rh
	ensures res::rb<1+ln+rn,c1,lh> & 0 <= c1 <= 1;
{
	// ensure left-leaning property
	if (h != null) {
	
		if (is_red(h.right))
			h = rotate_left(h);
		
		// eliminate two reds in a row
		if (h.left != null) {
			if (is_red(h.left) && is_red(h.left.left))
				h = rotate_right(h);
		}
	
		// push the red upward
		if (is_red(h.left) && is_red(h.right))
			color_flip(h);
	}		
	return h;
}

//////////////////////////////////////////
//           DELETE MINIMUM             //
//////////////////////////////////////////

// Delete the node with minimum value under h
// and return that minimum value.
int delete_min(node h)
	requires h::rb<n, cl, bh> & h != null
    case {
    	cl=1 -> ensures h::rb<n-1, cl2, bh>;
        cl=0 -> ensures h::rb<n-1, 0, bh2> & bh-1 <= bh2 <= bh;
        (cl<0 | cl>1) -> ensures false;
    }
{
	int m;
	
	if (h.left == null)
	{
		m = h.val;
		h = null;
	}

	if (!is_red(h.left) && !is_red(h.left.left))
		move_red_left(h);

	m = delete_min(h.left);

	fix_up(h);
	
	return m;
}

/*
//////////////////////////////////////////
//              DELETION                //
//////////////////////////////////////////

// Assuming that h is red and both h.right and h.right.left
// are black, make h.right or one of its children red.
void move_red_right(node h)
{
	color_flip(h);
	if (is_red(h.left.left)) { 
		rotate_right(h);
		color_flip(h);
	}
}

void delete(node h, int v)
	requires h::rb<n, cl, bh> & 0 <= cl <= 1
	ensures  h::rb<n-1, cl2, bh> & cl = 1 & 0 <= cl2 <= 1
		     or h::rb<n-1, 0, bh2> & bh-1 <= bh2 <= h & cl = 0 
		     or h::rb<n, cl, bh>;
{
	if (v < h.val) {
		if (!is_red(h.left) && !is_red(h.left.left))
			move_red_left(h);
		delete(h.left, v);
	} else {
		if (is_red(h.left))
			rotate_right(h);
			
		if (v == h.val && (h.right == null))
			h = null;
		if (!is_red(h.right) && !is_red(h.right.left))
			move_red_right(h); 
		
		if (v == h.val)
			h.val = delete_min(h.right);
		else 
			delete(h.right, v);
	}
	
	fix_up(h);
}*/