/* selection sort */

data node {
	int val; 
	node next; 
}

//******************************* FOR SINGLE PRE/POST **************************************
bnd2<n, sm, bg, mi, S> == self::node<mi, null> & sm <= mi < bg & n = 1 & S = {mi} or
                       self::node<d, p> * p::bnd2<n-1, sm, bg, tmi, S1> & sm <= d < bg & mi = min(d, tmi) & S = union(S1, {d})
                    inv n >= 1 & sm <= mi < bg;

sll2<n, sm, lg, S> == self::node<sm, null> & sm = lg & n = 1 & S = {sm} or 
                  self::node<sm, q> * q::sll2<n-1, qs, lg, S1> & q != null & sm <= qs & S = union(S1, {sm})
               inv n >= 1 & sm <= lg; 


//******************************* FOR MULTIPLE PRE/POST **************************************
bnd1<sm, bg, mi> == self::node<mi, null> & sm <= mi < bg or
                    self::node<d, p> * p::bnd1<sm, bg, tmi> & sm <= d < bg & mi = min(d, tmi)
                    inv sm <= mi < bg;

sll<sm, lg> == self::node<sm, null> & sm = lg or
               self::node<sm, q> * q::sll<qs, lg> & q != null & sm <= qs
               inv sm <= lg;

ll<n, mi> == self::node<mi, null> & n = 1 or
	self::node<v, q> * q::ll<n-1, mi1> & mi = min(v, mi1) & n > 1
	inv n >= 1; 

ll1<mi, S> == self::node<mi, null> & S = {mi}
	or self::node<v, q> * q::ll1<mi1, S1> & mi = min(v, mi1) & S = union(S1, {v});	

//*******************************************************************************************
                 
int find_min(node x)
	//requires x::bnd2<n, s, l, mi, S> 
        //ensures x::bnd2<n, s, l, mi, S> & res = mi;
	//******************************* FOR MULTIPLE PRE/POST **************************************
	requires x::bnd1<s, l, mi> 
        ensures x::bnd1<s, l, mi> & res = mi;
	requires x::ll<n, mi> & n>0
        ensures x::ll<n, mi> & res = mi;
  	requires x::ll1<mi, S> 
  	ensures x::ll1<mi, S> & res = mi;
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else
	{		
		tmp = find_min(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}


void delete_min(ref node x, int a)
	/*requires x::bnd2<n, s, l, mi, S> & a = mi 
	ensures x' = null & n = 1 & s <= mi < l & S = {mi} or 
               x'::bnd2<n-1, s, l, mi1, S1> & mi1 >= mi & x' != null & n > 1 & S = union(S1, {mi});
	*/
	//******************************* FOR MULTIPLE PRE/POST **************************************
	
	requires x::bnd1<s, l, mi> & a = mi 
	ensures x' = null & s <= mi < l or x'::bnd1<s, l, mi1> & mi1 >= mi & x' != null;
	requires x::ll<n, mi> & a = mi
	ensures x' = null & n = 1 or x'::ll<n-1, mi1> & mi1 >= mi;
	requires x::ll1<mi, S> & a = mi
	ensures x' = null & S = {mi} or x'::ll1<mi1, S1> & mi1 >= mi & S = union(S1, {mi});
	
{
	if (x.val == a)
		x = x.next;
	else {
		bind x to (_, xnext) in {
			delete_min(xnext, a);
		}
	}
}

node selection_sort(ref node x)
	//requires x::bnd2<n, sm, lg, mi, S>  
	//ensures res::sll2<n, mi, l, S> & l < lg & x' = null;
	//***************************** FOR MULTIPLE PRE/POST ****************************************
	
	requires x::bnd1<sm, lg, mi> 
	ensures res::sll<mi, l> & l < lg & x' = null;
	requires x::ll<n, _> 
	ensures res::ll<n, _> & x' = null;
	requires x::ll1<mi, S>
	ensures res::ll1<mi, S> & x' = null;
	
{
	int minimum;
	node tmp, tmp_null = null;	

	minimum = find_min(x);
	delete_min(x, minimum);

	if (x == null)
		return new node(minimum, tmp_null);
	else
	{
		tmp = selection_sort(x);

		return new node(minimum, tmp);
	}
	
}

