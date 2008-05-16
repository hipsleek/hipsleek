/* insertion sort */

data node {
	int val; 
	node next; 
}


//******************************* PREDICATES **************************************

bnd<sm, bg> == self = null or 
               self::node<d, p> * p::bnd<sm, bg> & sm <= d < bg;

sll<sm, lg> == self::node<sm, null> & sm = lg or
               self::node<sm, q> * q::sll<qs, lg> & q != null & sm <= qs
               inv sm <= lg;

ll<n> == self = null & n = 0 or
	self::node<_, q> * q::ll<n-1> & n > 0
	inv n >= 0; 


ll1<S> == self = null & S = {}
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});

ll2<n, S, sm, bg> == self = null & S = {} & n = 0
	or self::node<v, q> * q::ll2<n1, S1, sm, bg> & n = n1+1 & S = union(S1, {v}) & sm <= v < bg
	inv n >= 0;

sll2<n, S, sm, lg> == self::node<sm, null> & n = 1 & sm = lg & S = {sm}
	or self::node<sm, r> * r::sll2<n1, S1, qs, lg> & n = n1+1 & sm <= qs & S = union(S1, {sm}) 
	inv n > 0 & sm <= lg;


//*******************************************************************************************

     
/* function to insert an element in a sorted list */
node insert(node x, int v)
	//******************************* MULTIPLE PRE/POST **************************************
	requires x::sll<xs, xl>  
  	ensures res::sll<sres, lres> & sres = min(v, xs) & lres = max(v,xl);
	requires x::ll<n> & n > 0
	ensures res::ll<n+1>;
	requires x::ll1<S> & S != {}
	ensures res::ll1<S1> & S1 = union(S, {v});
	
	//********************************* ONE PRE/POST ********************************************
	//requires x::sll2<n, S, xs, xl> 
	//ensures res::sll2<n+1, S1, sres, lres> & S1 = union(S, {v}) & sres = min(v, xs) & lres = max(v, xl);
{
        node tmp_null = null;
        node xn;

	if (v <= x.val) {	
		return new node(v, x);
	}
	else {	
		assume false;
		if (x.next != null)
		{
			//assume false;
                        xn = insert(x.next, v);
			x.next = xn;
			return x;
		}
		else
		{
			//assume false;
			x.next = new node(v, tmp_null);
			return x;
		}
	}
		
}

/* insertion sort */

void insertion_sort(node x, ref node y)
	//******************************* MULTIPLE PRE/POST **************************************
	
	requires x::bnd<sm1, bg1> * y::sll<sm2, bg2>
        ensures y'::sll<sm, bg> * x::bnd<sm1, bg1> & sm <= sm2 & bg >= bg2;
	requires x::ll<n1> * y::ll<n2> & n2 > 0
        ensures y'::ll<n1+n2> * x::ll<n1>;
	requires x::ll1<S1> * y::ll1<S2> & S2 != {}
	ensures y'::ll1<S> * x::ll1<S1> & S = union(S1, S2);
	
	//****************************** ONE PRE/POST ***********************************************
	//requires x::ll2<n1, S1, sm1, bg1> * y::sll2<n2, S2, sm2, bg2> & n2 > 0
	//ensures y'::sll2<n1+n2, S, sm, bg> * x::ll2<n1, S1, sm1, bg1> & S = union(S1, S2) & sm <= sm2 & bg >= bg2;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}














































