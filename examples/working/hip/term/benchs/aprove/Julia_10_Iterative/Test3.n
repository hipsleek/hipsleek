data node {
	int val; 
	node next;	
}

ll<n> == 
	self = null & n = 0 or 
	self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

node create (int n)
case {
	n<0 -> requires Loop ensures false;
	n>=0 -> requires Term[n] ensures res::ll<n>;
}
{
	if (n == 0)
		return null;
	else {
		int v = rand_int();
		return new node (v, create(n - 1));
	}
}

int length (node x)
requires x::ll<n>@L & Term[n]
ensures res=n;
{
	if (x == null)
		return 0;
	else
		return 1 + length(x.next);
}

void main ()
requires Term
ensures true;
{
	int s = rand_nat();

	node l1 = create(s);
	node l2 = create(s);
	node l3 = create(s*s);
	
	while (length(l1) + length(l2) + length(l3) * 5 > 0)
	requires l1::ll<n1> * l2::ll<n2> * l3::ll<n3>
	case {
		n1+n2+n3*5<=0 -> requires Term ensures l1'::ll<n1> * l2'::ll<n2> * l3'::ll<n3>;
		n1+n2+n3*5>0 -> case {
			exists (k1: n1=2*k1+1) -> 
				requires Term[n1+n2+n3*5]
				ensures l1'::ll<n1-1> * l2'::ll<n2> * l3'::ll<n3>;
			exists (k2: n1=2*k2) -> case {
				n2>n3 ->
					requires Term[n1+n2+n3*5]
					ensures l1'::ll<n1> * l2'::ll<n2-1> * l3'::ll<n3>;
				n2<=n3 -> case {
					n3=0 -> requires Term ensures l1'::ll<n1> * l2'::ll<n2> * l3'::ll<n3>;
					n3!=0 -> 
						requires Term[n1+n2+n3*5]
						ensures l1'::ll<n1+1> * l2'::ll<n2+1> * l3'::ll<n3-1>;
				}
			}
		}
	}
	{
		int ll1 = length(l1);
		int ll2 = length(l2);
		int ll3 = length(l3);

		if (ll1 % 2 == 1)
			l1 = l1.next;
		else if (ll2 > ll3)
			l2 = l2.next;
		else if (ll3 == 0)
			return;
		else {
			l1 = new node (rand_int(), l1);
			l2 = new node (rand_int(), l2);
			l3 = l3.next;
		}
	}
}

int rand_int ()
requires Term
ensures true;

int rand_nat ()
requires Term
ensures res>=0;
