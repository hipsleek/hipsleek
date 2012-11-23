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
rbt<n, cl> == 
	self = null & n = 0 & cl = 1 
	or self::node<v, cl, l, r> * l::rbt<ln, _> * r::rbt<rn, _> & cl=1 & n=1+ln+rn
	or self::node<v, 0, l, r> * l::rbt<ln, 1> * r::rbt<rn, 1> & cl = 0 & n = 1 + ln + rn 
 	inv n >= 0 & 0 <= cl <= 1;


// Check if h is a red node or not.
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

// Flip the color of a node and its two children.
void color_flip(node h)
	requires h::node<v,c,l,r> * l::node<lv,lc,ll,lr> * r::node<rv,rc,rl,rr>
	ensures h::node<v,1-c,l,r> * l::node<lv,1-lc,ll,lr> * r::node<rv,1-rc,rl,rr>;
{
	assert h != null;
	h.color        = 1 - h.color;
	h.left.color   = 1 - h.left.color;
	h.right.color  = 1 - h.right.color;
}

void color_black(node h)
	requires h::node<v,c,l,r> 
	ensures h::node<v,1,l,r> ;
{
  h.color        = 1;
}

// Make a right-leaning 3-node lean to the left.
node rotate_left(node h)
	requires h::node<v,c,l,r> * r::node<rv,0,rl,rr>
	ensures res::node<rv,c,h,rr> * h::node<v,0,l,rl> & res = r;
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
	ensures res::node<lv,c,ll,h> * h::node<v,0,lr,r> & res = l;
{
	node x = h.left;
	h.left = x.right;
	x.right = h;
	x.color = x.right.color;
	x.right.color = 0;
	return x;
}

node insert(node h, int v)
  requires h::rbt<n,1>
  ensures res::rbt<n+1,1>;
{
  node a = insert_aux(h,v);
  if (is_red(a)) {
    color_black(a);
  }
  return a;

}

node insert_aux(node h, int v)
  requires h::rbt<n,_>
  ensures res::rbt<n+1,_> & res!=null;




	//PROBLEM DETECTED: THIS POST-CONDITION CANNOT BE VERIFIED SIMPLY BECAUSE THE SYSTEM DOES NOT KNOW
	//THAT IT NEEDS TO PERFORM A CASE SWITCH ON c!
	//ensures res::rbc<n+1,1,bh,_> or res::rbc<n+1,1,bh+1,_>;



/*
// Compute the black height of a red black tree
int black_height(node h)
	requires h::rbc<_,_,bh,_>@I
	ensures res = bh;
{
	if (h == null)
		return 1;
	else
		return h.color + black_height(h.left);
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
          // ^^ verified in 2s
		c = 1 -> ensures res::rbc<n+1,1,bh,resc> & 1 <= resc <= 2;
          // FAIL still (fail with foo)
		c = 2 -> ensures res::rbc<n+1,1,bh,resc> & 2 <= resc <= 3; 
          // ^^ 35sec or res::rbc<n+1,1,bh,3>; 35sec
		c = 3 -> ensures res::rbc<n+1,0,bh,4>; 
          // FOLD FAILED! (succeed with help of foo 3.8s)
		(c < 0 | c >= 4) -> ensures res::rbc<n+1,0,bh,4> or res::rbs<n+1,bh>; 
          // FAILS - CASE ANALYSIS FAILED IN SLEEK (fail with foo)
	}
{
    //assume (c < 0 | c >= 4);
     assume c=1;
	
	if (h == null)
		return new node(v, 0, null, null); // RED node

	node l = h.left;
	node r = h.right;
	
	if (is_red(h.left))
		if (is_red(h.right))
			color_flip(h);
	
	if (v <= h.val) { // accept duplicates!
		h.left = insert_internal(h.left, v);
		if (is_red(h.left))
			if (is_red(h.left.left))
				h = rotate_right(h);
	} else {
		r = h.right;
		h.right = insert_internal(h.right, v);
		r = h.right;
		if (is_red(h.right))
			if (!is_red(h.left))
				h = rotate_left(h);
	}
	
	// case c = 3 ==> folding error here!
 	//assert h'::node<_,0,lx,rx> * lx::rbc<ln,1,bh,_> * rx::rbc<rn,1,bh,_> & ln + rn = n; //' ok
    //assert h'::node<_,0,lx,rx> * lx::rbc<ln,0,bh,_> * rx::rbc<rn,0,bh,_> & ln + rn = n; //' failed
    //assert h'::node<_,1,lx,rx> * lx::rbc<ln,1,bh,_> * rx::rbc<rn,1,bh,_> & ln + rn = n; //' failed
 	//assert h'::rbc<_,_,_,_>;
	// case c = 4 ==> folding error + case analysis fail detected in sleek
	//assert h'::node<_,0,lx,rx> * lx::rbc<ln,_,bh,_> * rx::rbc<rn,1,bh,_> & ln + rn = n; //'
    //assume false;
	foo(h);
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
	case {
		c = 2 -> ensures res::rbc<n-1,1,bh,2> or res::rbc<n-1,1,bh,1>;
		c = 3 -> ensures res::rbc<n-1,1,bh,3> or res::rbc<n-1,1,bh,2>;
		// the following case is actually just c = 4 as 2 <= c <= 4 is in the assumption
		(c < 2 | c >= 4) -> case {
			n = 1 -> ensures res::rbc<n-1,1,bh,0> & bh = 1;
			n != 1 -> ensures res::rbc<n-1,0,bh,4> or res::rbc<n-1,1,bh,3>;
		}
	}
{
	assume c = 4;
	
	if (h.left == null) {
		min_value = h.val;
		return null;
	}

	node l = h.left;	
	// IDENTIFY WHICH CASE THE LEFT TREE IS, THIS INFORMATION IS IN rblc.
	int rblc;
	if (is_red(l.left)) {
		if (is_red(l.right))
			rblc = 3; // success! 9s
		else
			rblc = 2; // success! 48s
	} else
		rblc = 1;
	//assert l'::rbc<_,_,_,rblc'>;
	//assert 1 <= rblc' <= 3;
	
	assume rblc' = 1;

	if (!is_red(h.left))
		if (!is_red(h.left.left))
			h = move_red_left(h);
	
	l = h.left;
	
	int hc = h.color;
//	assume hc' = 0; // success! 92.385772
	assume hc' = 1;
//	assert l'::rbc<ln,0,bh-1,4> & ln >= 1 & hc' = 1 
//		or l'::rbc<ln,1,bh,2> & ln >= 1 & hc' = 0; // holds when rblc' = 1
//	assert l'::rbc<ln,1,bh,2> & ln >= 1; // holds when rblc' = 2
//	assert l'::rbc<ln,1,bh,3> & ln >= 1; // holds when rblc' = 3

	h.left = delete_min_internal(h.left, min_value);
	
	l = h.left;
//	node r = h.right;
//	assert h'::node<_,_,l',r'> * r'::rbc<_,1,bh,_>;

//	assert l'::rbc<_,_,bh-1,_> & hc' = 1 or l'::rbc<_,_,bh,_> & hc' = 0; // holds when rblc' = 1
//	assert l'::rbc<_,_,bh,2> or l'::rbc<_,_,bh,1>; // holds when rblc' = 2
//	assert l'::rbc<_,_,bh,3> or l'::rbc<_,_,bh,2>; // holds when rblc' = 3
	
//	bool rr = is_red(h.right);
//	assert !rr';
	
	//int leftheight = black_height(h.left);
	//assert leftheight' = bh - 1;
	
	assume l' != null;
	if (is_red(l)) {
		rblc = 4;
	} else 	if (is_red(l.left)) {
		if (is_red(l.right))
			rblc = 3;
		else
			rblc = 2;
	} else
		rblc = 1;
	assume rblc' = 3;
	
	if (is_red(h.right))
		if (!is_red(h.left))
			h = rotate_left(h);
		else
			assert false;
	else
		assert false;
	
//	l = h.left;
//	r = h.right;
//	assert h'::node<_,0,l',r'> * l'::rbc<rn,1,bh,_> * r'::rbc<ln,1,bh,_> & rn + ln + 1 = n - 1; // holds when rblc' = 2 or rblc' = 3
//	assert l'::rbc<_,_,bh,2> or l'::rbc<_,_,bh,1>; // holds when rblc' = 2
//	assert l'::rbc<_,_,bh,3> or l'::rbc<_,_,bh,2>; // holds when rblc' = 3

	return h;
}

//////////////////////////////////////////
//              DELETION                //
//////////////////////////////////////////

// Fix the invariant
node fix_up(node h)
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
	if (v < h.val) { // this branch is verified in 113.743108 second(s)
		if (h.left != null) {
			// case c = 4 requires the case analysis
			assert c != 4 or  l'::rbc<_,1,_,_>;
			assume c != 4 or l'::rbc<_,1,_,0> or l'::rbc<_,1,_,1> 
				or l'::rbc<_,1,_,2> or l'::rbc<_,1,_,3>;
			
			if (!is_red(h.left) && !is_red(h.left.left))
				h = move_red_left(h);
			
			h.left = delete_internal(h.left, v);
			
			//fix_up(h); 
			// what could possibly go wrong? only the left-leaning property!
			if (is_red(h.right) && !is_red(h.left))
				h = rotate_left(h);
		}
	} else {
		assume c = 2;
		int x = h.val;
		assume v >= x;
		
		if (v >= h.val) { // v >= h.val
			node l = h.left;
			assert l'::rbc<_,0,_,_>;
			
			if (is_red(h.left))
				h = rotate_right(h);
	
			if (v == h.val && (h.right == null))
				h = null;
			
			if (!is_red(h.right) && !is_red(h.right.left))
				h = move_red_right(h); 
			
			if (v == h.val) {
				int m;
				node r = h.right;
				assert r' != null;
				h.right = delete_min(h.right, m);
				// and set the value
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
*/
