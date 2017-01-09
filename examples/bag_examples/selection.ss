/* selection sort */

data node {
	int val; 
	node next; 
}
/*bnd1<n, sm, bg, mi> == self::node<mi, null> & sm <= mi < bg & n = 1 or
                       self::node<d, p> * p::bnd1<n1, sm, bg, tmi> & n = n1+1 & sm <= d < bg & mi = min(d, tmi)
                    inv n >= 0 & sm <= mi < bg;*/

bnd1<n, sm, bg, mi> == self::node<mi, null> & sm <= mi < bg & n = 1 or
                       self::node<d, p> * p::bnd1<n1, sm, bg, tmi> & n = n1+1 & sm <= d < bg & (d > tmi | mi = d) & (d <= tmi | mi = tmi) 
		/*       self::node<d, p> * p::bnd1<n1, sm, bg, tmi> & n = n1+1 & sm <= d < bg & mi = tmi & tmi < d	 */
                    inv n >= 0 & sm <= mi < bg;

sll<n, sm, lg> == self::node<sm, null> & sm = lg & n = 1 or 
                  self::node<sm, q> * q::sll<n1, qs, lg> & n = n1+1 & q != null & sm <= qs
               inv n >= 1 & sm <= lg; 

ll<n> == self::node<v, null> & n=1
	or self::node<v, r>* r::ll<m> & n=m+1 & n>=1;


ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));

//------------------------------------------------------------------------------------------
// find_min functions
//------------------------------------------------------------------------------------------

int find_min0(node x)
	requires x::bnd1<n, s, l, mi> & n>0
  	ensures x::bnd1<n, s, l, mi> & res = mi;
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else {		
		tmp = find_min0(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}

int find_min(node x)
	requires x::ll<n> & n>=1
  ensures x::ll<n>;
{o
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


int find_min1(node x)
requires x::bnd1<n, s, l, mi> & n>0
ensures x::bnd1<n, s, l, mi> & res = mi;
requires x::ll1<S> & x != null
ensures x::ll1<S> & res in S & forall (a: (a notin S | res <= a)); // bagmin(res, S);
{
	int tmp; 

	if (x.next == null)
		return x.val;
	else
	{		
		tmp = find_min1(x.next);
		if (tmp > x.val)
			return x.val;
		else
			return tmp;
	}
}
  

     
//------------------------------------------------------------------------------------------
// delete_min functions
//------------------------------------------------------------------------------------------

void delete_min0(ref node x, int a)
	requires x::bnd1<n, s, l, mi> & n >= 1 & a = mi 
	ensures x' = null & n = 1 & mi >= s & mi < l or 
  	x'::bnd1<n1, s, l, mi1> & n=n1+1 & mi1 >= mi & x' != null & n > 1;

{
	if (x.val == a)
		x = x.next;
	else {
		bind x to (_, xnext) in {
			delete_min0(xnext, a);
		}
	}
}

void delete_min(ref node x, int a)
	requires x::ll<n> & n >= 1  
	ensures x'=null or x'::ll<n1>;

{
	if (x.val == a)
		x = x.next;
	else { 
		if (x.next != null)
			//delete_min(x.next, a);
			bind x to (_, xnext) in {
				delete_min(xnext, a);
			}
	}
}

void delete_min1(ref node x, int a)
	requires x::bnd1<n, s, l, mi> & n >= 1 & a = mi 
	ensures x' = null & n = 1 & mi >= s & mi < l or 
  	x'::bnd1<n1, s, l, mi1> & n=n1+1 & mi1 >= mi & x' != null & n > 1;
	requires x::ll1<S> & a in S & x != null// bagmin(a, S)
	ensures x'::ll1<S1> & S = union(S1, {a});
{
	if (x.val == a)
		x = x.next;
	else { 
		if (x.next != null)
			bind x to (_, xnext) in {
				delete_min1(xnext, a);
			}
	}
}


//------------------------------------------------------------------------------------------
// selection_sort functions
//------------------------------------------------------------------------------------------

node selection_sort0(ref node x)
	requires x::bnd1<n, sm, lg, mi> & n > 0 
	ensures res::sll<n, mi, l> & l < lg & x' = null;

{
	int minimum;
	node tmp, tmp_null = null;	

	minimum = find_min0(x);
	delete_min0(x, minimum);

	if (x == null)
		return new node(minimum, tmp_null);
	else
	{
		tmp = selection_sort0(x);

		return new node(minimum, tmp);
	}
}


node selection_sort1(ref node x)
	requires x::bnd1<n, sm, lg, mi> & n > 0 
	ensures res::sll<n, mi, l> & l < lg & x' = null;
	requires x::ll1<S> & x != null 
	ensures res::sll1<S> & x' = null;

{
	int minimum;
	
	minimum = find_min1(x);
	if (x == null) 
		return null;
	else {
		delete_min1(x, minimum);

		if (x == null)
			return new node(minimum, null);
		else
		{  
			return new node(minimum, selection_sort1(x));
		}
	}
}












