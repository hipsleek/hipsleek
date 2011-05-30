/**
 Left-leaning Red Black Tree
 Modified from RedBlackBST.java
 @author: Vu An Hoa
 */


/*

hip --eps works, but

hip without --eps results in the following overflow:

Stop Omega... 1753 invocations 
Procedure insert_aux$node~int FAIL-2

ExceptionEnd_of_fileOccurred!

With --eps, we got many "h22" output.
What do they signify? why were they present?
h22
h22
h22
h22

Why is ctx of the OCtx form inside inner entailer?

*/



data node {
	int val;
	int color; /* 0 for red, 1 for black */
	node left;
	node right;
}


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
	requires h::node<v,1,l,r> * l::node<lv,0,ll,lr> * r::node<rv,0,rl,rr>
	ensures h::node<v,0,l,r> * l::node<lv,1,ll,lr> * r::node<rv,1,rl,rr>;
	requires h::node<v,0,l,r> * l::node<lv,1,ll,lr> * r::node<rv,1,rl,rr>
	ensures h::node<v,1,l,r> * l::node<lv,0,ll,lr> * r::node<rv,0,rl,rr>;
{
	h.color        = 1 - h.color;
	h.left.color   = 1 - h.left.color;
	h.right.color  = 1 - h.right.color;
}

// R-R-B -> R B R

node rotate_RRB(node h)
  requires h::node<v1,0,l,t3> * l::node<v2,0,t1,t2> 
  ensures res::node<v2,0,t1,r> * r::node<v1,0,t2,t3>; //
{
  node L  = h.left;
  //node T1=L.left;
  node T2 = L.right;
  //node T3=h.right;
  L.right = h;
  h.left = T2;
  return L;
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


node insert2(node h, int v)
//requires h::rbd<n,_,_,bh>
//ensures res::rbd<n+1,1,_,bh2> & bh<=bh2<=bh+1; //or res::rb<n+1,1,bh+1>;
  requires h::rbd<n,_,_,bh>
  ensures res::rbd<n+1,_,_,bh2> & bh<=bh2<=bh+1; //or res::rb<n+1,1,bh+1>;
{
  node r = insert_aux(h,v);
  if (is_red(r)) inc_rb_ht(r);
  return r;
}

// Insert a value v to an INTERNAL node of a red-black tree.
// Remark: NO height increment.
node insert_aux(node h, int v)
  case {
  h=null -> ensures res::node<v,0,null,null>;
   h!=null -> requires h::rbd<n,c,d,bh>
    case {
     c=1 -> case {
       d=0 ->  ensures res::rbd<n+1,0,1,bh> ; // R - error otherwise
       d!=0 ->  ensures res::rbd<n+1,1,_,bh>; // B - error otherwise
       }
     c!=1 -> ensures res::red<n+1,bh> & res!=null or res::rbd<n+1,0,1,bh> ;
   }
 }
{
   bool flip_flag=false;
   if (h == null) {
    node k=new node(v, 0, null, null);
    return k; 
  }	else {
     //bool orig_red = is_red(h); 
	if (is_red(h.right)) {
        color_flip(h); flip_flag=true;
    }
	if (v <= h.val) // accept duplicates!
      { 
        h.left = insert_aux(h.left, v);
      }
	else h.right = insert_aux(h.right, v);

   if (is_red(h)) {
     //dprint;
     //assume false;
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
        //dprint;
        //assume false; 
        //assert x'!=null; //'
        node xleft=x.left;
        node xright=x.right;
        if (is_red(xleft)) {
          //assert xleft'::rbd<_,0,_,_>; //' ok
          //assert xright'::rbd<_,1,_,_>; //'  ok
          //assert y'::rbd<_,1,_,_>; //'  ok
           //assume false;
           h=double_rotate(h);
        }
        } 
      else {
        // h is BBX
        //dprint;
        //assume false;
        //assert x'::rbd<_,1,_,_>; //'  ok
        if (is_red(h.right)) {
        // h is BBR
          //assert y'::rbd<_,0,_,_>; //' ok
          h=rotate_left(h);
        } 
        /* else {
          // h is BBB
          //assert y'::rbd<_,1,_,_>; //' ok
           //dprint;
          assume true;
          //assume false;
          } 
         */
       }
 }
  return h;
  }
}


