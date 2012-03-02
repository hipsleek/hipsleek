/* binary search trees */

data node2 {
	int val;
	node2 left;
	node2 right; 
}


/* view for binary search trees */
bst <sm, lg> == self = null & sm <= lg 
	or (exists pl,qs: self::node2<v, p, q> * p::bst<sm, pl> * q::bst<qs, lg> & pl <= v & qs >= v)
	inv sm <= lg;


//relation A(int x, int y, int z).
relation B(int x, int y, int a, int b).


/* delete a node from a bst */

int remove_min(ref node2 x)
	requires x::bst<s, b> & x != null 
	ensures x'::bst<s1, b> & s <= res <= s1;

// TODO: problem with left-most node
void delete(ref node2 x, int a)
    infer [B]
	requires x::bst<sm, lg> 
    //ensures x'::bst<s, l> & sm <= s & l <= lg; 
    //ensures x'::bst<s, l> & sm <= s & l <= lg & B(sm,s,l,lg); 
    ensures x'::bst<s, l> & B(sm,s,l,lg); 

{
	int tmp; 

	if (x != null)
	{
        //assume false;
		bind x to (xval, xleft, xright) in 
		{
			if (xval == a) 
			{
				if (xright == null) {
                    //assert true;
          /*if (xleft == null){
            assume sm<=s;
            x = null;
          }
          else*/
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
        dprint;
	}
    else {
      assume true;
    }
}

