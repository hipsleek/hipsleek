/**
 Left-leaned Red Black Tree
 Modified from RedBlackBST.java
 @author: Vu An Hoa
 
 REMARK: THIS CODE IS COMPACT; YET IT IS "IMPOSSIBLE" TO WRITE THE SPECIFICATIONS
 FOR THESE FUNCTIONS. THE TRICK IS TO MIMICK THE ORIGINAL IMPLEMENTATION rb.ss BY
 MAKING EVERY FIELD ACCESS h.left, h.right INTO A PARAMETER. WHENEVER WE CALL THE
 FUNCTIONS, JUST ADD THE APPROPRIATE (EXPECTED) PARAMETERS.
 CONVERTED FUNCTIONS ARE MARKED WITH _alt EXTENSION.
 */

data node {
	int val;
	int color; /* 0 for red, 1 for black */
	node left;
	node right;
	int black_height; /* black height */
}

/* view for red-black trees */
rb<n, cl, bh> == self = null & n = 0 & bh = 1 & cl = 1
	or self::node<v, 0, l, r, bh> * l::rb<nl, 1, bhl> * r::rb<nr, 1, bhr>
       & cl = 0 & n = 1 + nl + nr & bhl = bh & bhr = bh
	or self::node<v, 1, l, r, bh> * l::rb<nl, _, bhl> * r::rb<nr, _, bhr>
       & cl = 1 & n = 1 + nl + nr & bhl = bhr & bh = 1 + bhl
	inv n >= 0 & bh >= 1 & 0 <= cl <= 1;

/*************************************
          HELPERS FUNCTIONS
 *************************************/

bool is_red(node h)
	requires h::rb<n, cl, bh>@I
	ensures cl = 1 & !res or cl = 0 & res;
{
  if (h==null) return false;
  else return (h.color==0);
}

void color_flip(ref node h)
  requires h::node<v,c,lt,rt,bh> * lt::node<v1,c1,llt,lrt,hl> * rt::node<v2,c2,rlt,rrt,hr> 
  ensures h::node<v,1-c,lt,rt,bh> * lt::node<v1,1-c1,llt,lrt,hl> * rt::node<v2,1-c2,rlt,rrt,hr>;
{  
	h.color        = 1 - h.color;
	h.left.color   = 1 - h.left.color;
	h.right.color  = 1 - h.right.color;
}



