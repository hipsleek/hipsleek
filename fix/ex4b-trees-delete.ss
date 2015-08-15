/* trees & binary search trees */


data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* binary search trees */

/* view for binary search trees */
bst <sm, lg> == self = null & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v)
	inv sm <= lg;



/* delete a node from a bst */

int remove_min(node2@R x)

	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1, b> & s <= res <= s1;


void delete(node2@R x, int a)

	requires x::bst<sm, lg> 
	ensures x'::bst<s, l> & sm <= s & l <= lg;

{
	int tmp; 

	if (x != null)
	{
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) 
			{
				if (xright == null) {
                    assert true;
					x = xleft; 
				}
				else
				{
					tmp = remove_min(xright);
					xval = tmp;
				}
			}
			else
			{
				if (xval < a)
					delete(xright, a);
				else
					delete(xleft, a);
			}
		}
	}
}

/*
# ex4b.ss

5 post-conditions proving. However, one of them was
actually false:

id: 26 src:5; caller: []; line: 30; classic: false; kind: POST; hec_num: 2; evars: []; infer_vars: [ ]; c_heap: emp; others: [] globals: [@flow,@ver_post]
 checkentail hfalse&false&{FLOW,(4,5)=__norm#E}[]
 |-  (exists s,l: x'::bst<s,l>@M&sm<=s & l<=lg&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  1[
    hfalse&false&{FLOW,(4,5)=__norm#E}[]
   ]

# We need to track where this came from; and have it screened
  earlier.

This will help minimise false UNSOUND warning below.

!!! **typechecker.ml#929:
 Before CheckPost : 5
!!! **typechecker.ml#930:
 After CheckPost : 4
[UNSOUNDNESS] WARNING : possible new unsatisfiable state from post-proving of ex4b-trees-delete.ss_30:9_30:42


*/
