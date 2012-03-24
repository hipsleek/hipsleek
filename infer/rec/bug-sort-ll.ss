/* binary search trees */

data node {
	int val;
	node next; 
}


/* view for binary search trees */
sll <sm, lg> == self = null & sm <= lg 
    or self::node<sm, p> * p::sll<s2, lg> & sm<=s2
	inv sm <= lg;


//relation A(int x, int y, int z).
relation B(int x, int y, int a, int b).


void delete(ref node x, int a)
    infer [B]
	requires x::sll<sm, lg> 
    ensures x'::sll<s, l> & sm <= s & l <= lg;//' 
   //ensures x'::bst<s, l> & B(sm,s,l,lg); //'

{
	int tmp; 

	if (x != null)
	{
      //assume false;
		bind x to (xval, xnext) in 
		{
			if (xval == a) 
			{
                x = xnext;
			}
			else
			{
				if (xval < a)
                    return;
				else
					delete(xnext, a);
			}
		}
        //dprint;
	}
    else {
      assume true;
    }
}

