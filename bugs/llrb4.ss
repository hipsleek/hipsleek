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
	or self::node<v, 1, l, r> * l::rb<ln, 0, lbh> * r::rb<rn, 0, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh
	or self::node<v, 1, l, r> * l::rb<ln, 0, lbh> * r::rb<rn, 1, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;

/* view for red-black trees */
rbd<n, cl, d, bh> == self = null & n = 0 & bh = 1 & cl = 1 & d=2  
    or self::node<v, 0, l, r> * l::rbd<ln, 1,_, lbh> * r::rbd<rn, 1,_, rbh>
	   & cl = 0 & n = 1 + ln + rn & lbh = bh & rbh = bh & d=1 
   or self::node<v, 1, l, r> * l::rbd<ln, _,_, lbh> * r::rbd<rn, 1,_, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh & d=1 
   or self::node<v, 1, l, r> * l::rbd<ln, 0,_, lbh> * r::rbd<rn, 0,_, rbh>
       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh & d=0 
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1 & 0 <= d <=2;
//   or self::node<v, 1, l, r> * l::rbd<ln, 1,_, lbh> * r::rbd<rn, 1,_, rbh>
//       & cl = 1 & n = 1 + ln + rn & lbh = rbh & bh = 1 + lbh & d=1 

red<n, bh> == self::node<_,0,t1,t2> * t1::rbd<n1,0,_,h1> * t2::rbd<n2,1,_,h2> 
                   & bh=h1 & bh=h2  & n=1+n1+n2 
  //          or  self::node<v, 0, l, r> * l::rbd<n1, 1,_, lbh> * r::rbd<n2, 1,_, rbh> &
  // 	              n = 1 + n1 + n2 & lbh = bh & rbh = bh 
	inv n >= 1 & bh >= 1 & self!=null;

void inc_rb_ht(node r)
  requires r::red<n,bh> or r::rbd<n,0,_,bh>
  ensures r::rbd<n,1,_,bh+1>;
//  requires r::node<v,0,l,r>
//  ensures r::node<v,1,l,r>;

{
  r.color = 1;
}

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
		h != null -> 
          requires h::node<v,c,l,r>@I
          ensures true & (c=0 & res | c!=0 & !res);
	}
*/
	case{
		h  = null -> ensures !res;
		h != null -> 
          requires h::node<v,c,l,r>
          ensures h::node<v,c,l,r> & (c=0 & res | c!=0 & !res);
	}
{
	if (h==null)
		return false;
	else
		return (h.color==0);
}

void color_flip(node h)
	requires h::node<v,c1,l,r> * l::node<lv,c2,ll,lr> * r::node<rv,c3,rl,rr>
	ensures h::node<v,1-c1,l,r> * l::node<lv,1-c2,ll,lr> * r::node<rv,1-c3,rl,rr>;
/*
 	requires h::node<v,1,l,r> * l::node<lv,0,ll,lr> * r::node<rv,0,rl,rr>
	ensures h::node<v,0,l,r> * l::node<lv,1,ll,lr> * r::node<rv,1,rl,rr>;
	requires h::node<v,0,l,r> * l::node<lv,1,ll,lr> * r::node<rv,1,rl,rr>
	ensures h::node<v,1,l,r> * l::node<lv,0,ll,lr> * r::node<rv,0,rl,rr>;
*/
{
	h.color        = 1 - h.color;
	h.left.color   = 1 - h.left.color;
	h.right.color  = 1 - h.right.color;
}

// R -> B
void change_R_to_B(node h)
  requires h::node<v1,0,t1,t2>  
  ensures h::node<v1,1,t1,t2> ;
{
  h.color = 1;
}

//  B-R[R(B1)(B2)](B3)-(B4) ==> B-R(B1)(B2)-R(B3)(B4) 
node double_rotate(node h)
  requires h::node<v3,c1,l,t4> * l::node<v2,c3,ll,t3> * ll::node<v1,c2,t1,t2>
  ensures res::node<v2,c1,l2,ll2> * l2::node<v1,c2,t1,t2> * ll2::node<v3,c3,t3,t4> ;
//  B(v1)-B1-R(v2)(B2)(B3) ==> B(v2)-R(v1)(B1)(B2)-B3   
//  R(v1)-B1-R(v2)(B2)(B3) ==> R(v2)-R(v1)(B1)(B2)-B3
// BBR -> BRB 
// node rotate_left(node h)
//  requires h::node<v1,c1,t1,r> * r::node<v2,0,t2,t3> 
//  ensures res::node<v2,c1,l,t3> * l::node<v1,0,t1,t2>; //

// Make a right-leaning 3-node lean to the left.
// PROBLEM DETECTED: SPECIFICATION FAILURE

node rotate_left(node h)
	requires h::node<v,c,t1,r> * r::node<rv,0,t2,t3>
	ensures res::node<rv,c,h,t3> * h::node<v,0,t1,t2> & res = r;
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
//requires h::rbd<n,_,_,bh>
//ensures res::rbd<n+1,1,_,bh2> & bh<=bh2<=bh+1; //or res::rb<n+1,1,bh+1>;
  requires h::rbd<n,_,_,bh>
  ensures res::rbd<n+1,_,_,bh2> & bh<=bh2<=bh+1; //or res::rb<n+1,1,bh+1>;
{
  node r = insert_aux(h,v);
  if (is_red(r)) change_R_to_B(r); //inc_rb_ht(r);
  return r;
}

// Insert a value v to an INTERNAL node of a red-black tree.
// Remark: NO height increment.
node insert_aux(node h, int v)
  case {
  h=null -> ensures res::node<v,0,null,null>;
  h!=null -> requires h::rbd<n,c,d,bh> //& h!=null
    case {
     c=1 -> case {
       d=0 ->  ensures res::rbd<n+1,0,1,bh> ; //& n>0 ; //& res!=null; // R
       //res::node<_, 0, l, r> * l::rbd<ln, 1,_, bh> * r::rbd<n-ln, 1,_, bh>;
       d!=0 ->  ensures res::rbd<n+1,1,_,bh>; // & n>0 ; // B // loop here
       //res::node<_, 1, l, r> * l::rbd<ln1, _,_, bh-1> * r::rbd<n-ln1, 1,_, bh-1>
       //or res::node<_, 1, l, r> * l::rbd<ln2, 0,_, bh-1> * r::rbd<n-ln2, 0,_, bh-1>  ;
       }
     c!=1 -> ensures res::red<n+1,bh> //& res!=null 
            or res::rbd<n+1,0,1,bh> //& res!=null
       ;
   }
 }
{
  //bool flip_flag=false;
   if (h == null) {
    node k=new node(v, 0, null, null);
    return k; 
  }	else {

    if (!is_red(h)) {
	if (is_red(h.right)) {
      color_flip(h); //flip_flag=true;
    } else {
      assume true;
      // assume false;
    }
    }
	if (v <= h.val) // accept duplicates!
      { 
        h.left = insert_aux(h.left, v); 
      }
	else h.right = insert_aux(h.right, v);
   if (is_red(h)) {
     // RBB or BRR->RBB
     if (is_red(h.right)) {
       h=rotate_left(h);}
   } else {
     // assumes h is now black
     // h was BXB
      node x=h.left;
      node y=h.right;
      if (is_red(h.left)) {
        // h is BRB
        node xleft=x.left;
        node xright=x.right;
        if (is_red(xleft)) {
           h=double_rotate(h);
        }
        } 
      else {
        if (is_red(h.right)) {
        // h is BBR
          //assert y'::rbd<_,0,_,_>; //' ok
          h=rotate_left(h);
        } 

       }
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
	requires h::node<v,c,l,r> * l::rb<ln,lc,lh> 
           * rt::rb<rn,rc,rh> & 0 <= c <= 1
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
     * rt::node<rv,1,rlt,rrt> * rlt::rbd<n,c,_,bh>
    case {
     c=1 -> ensures  h::node<v,1,lt,rt> * lt::node<lv,0,llt,lrt> 
                  * rt::node<rv,0,rlt,rrt> * rlt::rbd<n,c,_,bh>;
     c=0 ->

      * llt::node<llv,1,lllt,llrt> 
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



int delete_min(ref node h)
  requires h::rbd<n,1,d,bh> & n>=1
  ensures h'::rbd<n-1,_,_,bh2> & bh-1<=bh2<=bh ; //'
  requires h::rbd<n,0,d,bh> & n>=1
  ensures h'::rbd<n-1,_,_,bh2> & bh-1<=bh2<=bh ; //'
{
  if (!is_red(h)) {
      if (!is_red(h.left)) {
          h.color = 0;
      }
  }
  int v=delete_min_aux(h);
  if (is_red(h)) {
    h.color = 1;
  }
  return v;
}

int delete_min_aux(ref node h)
  requires h::node<_,c,l,r> * l::rbd<n1, c1, _,bh> * r::rbd<n2, c2, _,bh> & 0<=c<=1
  case {
    c=0 ->
      requires c2=1 
      case {
        l=null -> ensures h'=null;
        l!=null -> ensures h'::rbd<n1+n2,_,_,bh> ;
      }
    c!=0 ->
      requires c1=0
      ensures h'::rbd<n1+n2,_,_,bh+1> or h'::red<n1+n2,bh-1> ; //'
  }
/*
& h != null
    case {
    	cl=1 -> ensures h::rb<n-1, cl2, bh>;
        cl=0 -> ensures h::rb<n-1, 0, bh2> & bh-1 <= bh2 <= bh;
        (cl<0 | cl>1) -> ensures false;
    }
*/
{
	int m;
	
	if (h.left == null)
	{
		m = h.val;
		h = null;
        return m;
	}
    assume false;
	if (!is_red(h.left) && !is_red(h.left.left))
      color_flip(h);
      //move_red_left(h);

	m = delete_min_aux(h.left);

	fix_up(h);
	
	return m;
}

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
}

