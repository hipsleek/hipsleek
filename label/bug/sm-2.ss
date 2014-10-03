/* selection sort */

data node {
	int val; 
	node next; 
}

bnd1<"n":n, "v":sm, "v":bg, "v":mi> == 
	self::node<mi, null> & ["n":n=1; "v":sm <= mi < bg] or
	self::node<d, p> * p::bnd1<n1, sm, bg, tmi> & ["n":n1=n-1; "v":sm <= d < bg & mi = min(d, tmi)]
        inv true & ["n":n >= 0; "v":sm <= mi < bg];

sll<"n":n, "v":sm, "v":lg> == 
	self::node<sm, null> & ["n":n=1; "v":sm = lg] or 
        self::node<sm, q> * q::sll<n1, qs, lg> & q != null & ["n":n1=n-1; "v":sm <= qs]
        inv true & ["n":n >= 1; "v":sm <= lg]; 

                 
int find_min(node x)
  requires x::bnd1<n, s, l, mi> & ["n":n>0]
  ensures x::bnd1<n, s, l, mi> & ["v",""@I:res = mi];
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
  requires x::bnd1<n, s, l, mi> & ["n":n >= 1; "v","":a = mi] 
  ensures x' = null & ["n":n = 1; "v":s <= mi < l] or 
            x'::bnd1<n1, s, l, mi1> & x' != null & ["n":n>1 & n1=n-1; "v":mi1 >= mi];//'

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
	requires x::bnd1<n, sm, lg, mi> & ["n":n > 0] 
	ensures res::sll<n, mi, l> & ["v":l < lg];

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












