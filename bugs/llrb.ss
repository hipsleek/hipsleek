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

/* view for red-black trees */
rbd<n, cl, d, bh> == self = null & n = 0 & bh = 1 & cl = 1 & d=0
	// self is red, both child must be black
    or self::node<v, 0, l, r> * l::rbd<ln, 1,_, lbh> * r::rbd<rn, 1,_, rbh>
	   & cl = 0 & n = 1 + ln + rn & lbh = bh & rbh = bh & d=1
   // if left is black, right must be black due to left-leaning!
   or self::node<v, 1, l, r> * l::rbd<ln, 1,_, lbh> * r::rbd<rn, 1,_, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh & d=1
   or self::node<v, 1, l, r> * l::rbd<ln, 0,_, lbh> * r::rbd<rn, 1,_, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh & d=2
   or self::node<v, 1, l, r> * l::rbd<ln, 0,_, lbh> * r::rbd<rn, 0,_, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh & d=3
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1 & 0 <= d <=3;


//////////////////////////////////////////
//          HELPER FUNCTIONS I          //
//////////////////////////////////////////
// Specification node naming convention:
// h : main node
// lt : left tree; rt : right tree
// llt : lt's left tree; rlt : rt's left tree; ...


bool is_red(node h)
/*
	case{
		h  = null -> ensures !res;
		h != null -> requires h::node<v,c,l,r>
		             ensures h::node<v,c,l,r> & c != 0 & !res 
		                     or h::node<v,c,l,r> & c = 0 & res;
	}
*/
	case{
		h  = null -> ensures !res;
		h != null -> 
          requires h::node<v,0,l,r> ensures h::node<v,0,l,r> & res;
          requires h::node<v,1,l,r> ensures h::node<v,1,l,r> & !res;
	}
{
	if (h==null)
		return false;
	else
		return (h.color==0);
}

void color_flip(node h)
//requires h::node<v,c,l,r> * l::node<lv,lc,ll,lr> * r::node<rv,rc,rl,rr>
//	ensures h::node<v,1-c,l,r> * l::node<lv,1-lc,ll,lr> * r::node<rv,1-rc,rl,rr>;
	requires h::node<v,1,l,r> * l::node<lv,0,ll,lr> * r::node<rv,0,rl,rr>
	ensures h::node<v,0,l,r> * l::node<lv,1,ll,lr> * r::node<rv,1,rl,rr>;
{
	h.color        = 1 - h.color;
	h.left.color   = 1 - h.left.color;
	h.right.color  = 1 - h.right.color;
}

// Make a right-leaning 3-node lean to the left.
// PROBLEM DETECTED: SPECIFICATION FAILURE
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
// PROBLEM DETECTED: SPECIFICATION FAILURE
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

// compute the black height of a red black tree
int black_height(node h)
	requires h::rb<_,_,bh>
	ensures res = bh;
    requires h::rbd<_,_,_,bh>
	ensures res = bh;
{
	if (h == null)
		return 1;
	
	if (is_red(h))
		return black_height(h.left);
	else
		return 1 + black_height(h.left);
}

//////////////////////////////////////////
//              INSERTION               //
//////////////////////////////////////////

// Insert a value v to the ROOT node of a red-black tree
// Remark: POSSIBLE to have height increment.
node insert(node h, int v)
  requires h::rbd<n,_,_,bh>
  ensures res::rbd<n+1,1,_,bh2> & bh<=bh2<=bh+1; //or res::rb<n+1,1,bh+1>;
{
	node r = insert_internal(h,v);
	if (is_red(r)) r.color = 1;
	return r;
}

// Insert a value v to an INTERNAL node of a red-black tree.
// Remark: NO height increment.
node insert_internal(node h, int v)
	// the following is not strong enough
	//requires h::rb<n,c,bh>
	//ensures res::rb<n+1,0,bh> or res::node<_,0,l,r> * l::rb<ln,0,bh> * r::rb<rn,1,bh> & ln + rn = n;
/*
	requires h::rb<n,c,bh>
	case {
		h  = null -> ensures res::rb<1,0,1>;
		h != null -> requires h::node<_, c, l, r> * l::rb<_,lc,_> * r::rb<_,rc,_>
		case {
			c = 1 & lc = 1 & rc = 1 -> ensures res::rb<n+1,1,bh>; // h, l, r are all black nodes
			c = 1 & lc = 1 & rc != 1 -> ensures false;
			c = 1 & lc != 1 & rc = 1 -> ensures res::rb<n+1,1,bh>; // h, r are black, l is red
			c = 1 & lc != 1 & rc != 1 -> ensures res::rb<n+1,0,bh> // h is black with two red children
			    or res::node<_,0,l1,r1> * l1::rb<ln1,0,bh> * r1::rb<rn1,1,bh> & ln1 + rn1 = n;
			c != 1 & lc = 1 & rc = 1 -> ensures res::rb<n+1,0,bh> // h is red with two black children
			    or res::node<_,0,l1,r1> * l1::rb<ln1,0,bh> * r1::rb<rn1,1,bh> & ln1 + rn1 = n;
			c != 1 & (lc != 1 | rc != 1) -> ensures false;
		}
	}

  requires h::rbd<n,c,d,bh> & h=null
  ensures res::rbd<1,0,_,1>;
*/

  case {
   h=null -> ensures res::rbd<1,0,1,1>;
   h!=null -> 
    requires h::rbd<n,c,d,bh>
    case {
     c=1 -> case {
             1<=d<=2 ->   ensures res::rbd<n+1,1,_,bh>; /* cannot be proven yet */
              d=3 ->  ensures res::rbd<n+1,0,_,bh>;
             (d<1 | d>3)  ->  ensures false;
             //d>3 ->  ensures false;
            }
     c=0 -> case {
       d=1 ->  ensures res::rbd<n+1,1,_,bh>; //false; //res::node<_,0,lt,rt> * lt::rbd<_,_,_,_> * rt::rbd<_,_,_,_> ; //& bh<=bh2<=bh+1;
       d!=1 -> ensures false;
            }
     (c<0 | c>1)  -> ensures false;
     //c>1 -> ensures false;
   }
 }
{
  if (h == null) {
    //assert c=1 & bh=0;
    node k=new node(v, 0, null, null);
    //dprint;
    //assert k'::rbd<1,0,_,1>;
    return k; //new node(v, 0, null, null); // RED node

  }	else {
	node l = h.left;
	node r = h.right;
	//dprint;
	// split this node if it is a 4 node
	if (is_red(h.left) && is_red(h.right)) {
      //dprint;
        //assert h'::node<_,1,_,_> ;
        //rb<_,0,bh-1> * r'::rb<_,0,bh-1> & l' != null & r' != null;
        color_flip(h);
        //assert h'::node<_,0,_,_> ;
		//h.color        = 0;
		//h.left.color   = 1;
		//h.right.color  = 1;
		//assert h'::rb<n,0,bh>;
		//assert l'::rb<_,1,bh> * r'::rb<_,1,bh>;

	} 
	
	// REMARK: THE COLOR OF THE RESULTING NODE IS DETERMINED HERE
	// BECAUSE ROTATION DOES NOT CHANGE COLOR OF THE RESULTING NODE!
	// THUS, h IS RED OR h IS BLACK WITH 2 RED CHILDREN ==> res IS RED
	// OTHERWISE, res IS A BLACK NODE

	// after splitting 4 nodes, the right branch is ALWAYS BLACK!
	//assert h'::node<_,_,_,_>;
	//assert r'::rbd<_,1,_,_>;
	//dprint;
	if (v <= h.val) // accept duplicates!
      { 
        h.left = insert_internal(h.left, v);
      }
	else
	 h.right = insert_internal(h.right, v);
		
	// IF THIS BRANCH IS NOT TAKEN, THE FOLLOWING if IS NEVER EXECUTED
	// BECAUSE IN SUCH CASE h.right IS NOT MODIFIED. AND WE KNOW THAT
	// h.right IS BLACK BEFORE THIS if-then-else. (THE STATEMENT
	// h.left = insert(l, v);
	// POTENTIALLY CHANGES THE COLOR OF h.left; BUT NOT h.right!)
	if (is_red(h.right)) {
       //assume false;	
		h = rotate_left(h);
    } 
	
	// convert R-R-B into B-R-R
	if (is_red(h.left)) {
		if (is_red(h.left.left)) {
          //assume false;
			h = rotate_right(h);
		} 
        else {
          assume false; // goes into a loop otherwise!
          //assume true;
        }
	} else {
      assume false; // goes into a loop otherwise!
      //assume true;
    }
    //dprint;

		
	return h;
  }
}

//////////////////////////////////////////
//         HELPER FUNCTIONS II          //
//////////////////////////////////////////

// Fix the invariant
node fix_up(node h)
	requires h::node<v,c,l,r> * l::rb<ln,lc,lh> * rt::rb<rn,rc,rh> & 0 <= c <= 1
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

node xx(node h, int v)
/*
 case {
  h=null ->   ensures res::rb<1,0,1>;
  h!=null ->  requires h::rb<n,c,bh> & n>0
              ensures true;
  }
*/
  
  case {
   h=null -> ensures res::rbd<1,0,1,bh>;
   h!=null -> requires h::rbd<n,c,d,bh>
    case {
     c=1 -> case {
              d=1 ->  requires false ensures false; 
              //res::rbd<n+1,1,_,bh>; /* cannot be proven yet */
              d=2 ->  ensures res::node<_,0,lt,rt>;
              // * lt::rbd<_,0,_,_> * rt::rbd<_,0,_,_>; 
              //ensures res::rbd<n+1,0,_,bh>;
              d<1 ->  ensures false;
              d>2 ->  ensures false;
            }
     c=0 -> case {
       d=1 -> requires false ensures false ;
              //res::node<_,1,lt,rt> * lt::rbd<_,0,_,_> * rt::rbd<_,0,_,_> ;
              //& bh<=bh2<=bh+1;
       d!=1 -> ensures false;
            }
      c<0 -> ensures false;
      c>1 -> ensures false;
   }
 }

{
  if (h == null) {
    node k=new node(v, 0, null, null);
    //dprint;
    //assert k'::rbd<1,0,_,1>;
    return k; //new node(v, 0, null, null); // RED node
  }	
  //assume false;
  //dprint;
  node l = h.left;
  //dprint;
  node r = h.right;
  //dprint;
  if (is_red(h.left) && is_red(h.right)) {
    //assert h'::node<_,1,_,_> ;
    color_flip(h);
    //assert l'!=null & r'!=null;
    dprint;
    assert h'::node<_,0,_,_> ;
    return h;
  }
  //dprint;
  assume false;
  return h;
}
