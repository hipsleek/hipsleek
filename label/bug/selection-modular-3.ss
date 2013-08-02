/* selection sort */

data node {
	int val; 
	node next; 
}

bnd1<"n":n, "v":sm, "v":bg, "v":mi> == 
  self::node<mi, null> & ["n","":n=1; "v","":sm <= mi < bg] or
  self::node<d, p> * p::bnd1<n1, sm, bg, tmi> & ["n","":n1=n-1; "v","":sm <= d < bg & mi = min(d, tmi)]
        inv true & ["n":n >= 0; "v":sm <= mi < bg];

sll<"n":n, "v":sm, "v":lg> == 
	self::node<sm, null> & ["n":n=1; "v":sm = lg] or 
        self::node<sm, q> * q::sll<n1, qs, lg> & q != null & ["n":n1=n-1; "v":sm <= qs]
        inv true & ["n":n >= 1; "v":sm <= lg]; 

                 
int find_min(node x)
  requires x::bnd1<n, s, l, mi> & ["","n":n>0]
  ensures x::bnd1<n, s, l, mi> & ["v":res = mi];
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












