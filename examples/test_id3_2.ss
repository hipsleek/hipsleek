data node{
	int val;
	node next;
}

ll<p, n> == self = p & n = 0 or 
            self::node<_, r> * r::ll<q, m> & p = q & n = m+1 & self != p
            inv n >= 0;


void id3(node x, node p, node r, int n)
	requires x::ll<r, i> * r::ll<p, j>   & n=i+j
	ensures x::ll<p, n>; // & n = i + j;
{

	if (x == p)
	{
		if (p==r){
			//assert n=0;
			//debug on;
			//dprint;
			assert x::ll<p, n>;
			//debug off;
		 	skip();
			return;
		}
                else {
			assume false;
		}
	}
	else {
		if (x != r)
			bind x to (v, z) in 
			{
				id3(z, p ,r, n-1);
				assume false;
			}
		else  {
			skip();
		}

		assume false;
	}
	

}

void skip() requires true ensures true;
