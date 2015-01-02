/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

pq<n, mx> == self = null & n = 0 & mx = 0 
	or self::node<d, n1, n2, l, r> * l::pq<n1, mx1> * r::pq<n2, mx2>
	& n = 1 + n1 + n2 & d >= 0 &  d >= mx1 & d >= mx2 & mx = d & 0 <= n1 - n2 <= 1
	inv n >= 0 & mx >= 0;

/* function to insert an element into a priority queue */
node insert(node t, int v)
	requires t::pq<n, mx> & v >= 0
	ensures res::pq<n1, ma> & n1 = n+1 & (v>=mx & ma = v | ma = mx & v<mx); /*ma = max(v, mx);*/ 
{
	node tmp, tmp_null = null; 
	int tmpv;

	if (t == null)
		return new node(v, 0, 0, tmp_null, tmp_null);
	else
		if (v > t.val)
		{
			if (t.nleft == t.nright)
			{
				t.left = insert(t.left, t.val);
				t.nleft++;
			}
			else 
			{
				t.right = insert(t.right, t.val);
				t.nright++;
			}
			t.val = v;
			return t;
		}
		else
		{
			if (t.nleft == t.nright)
			{
				t.left = insert(t.left, v);
				t.nleft++;
			}
			else 
			{
				t.right = insert(t.right, v);
				t.nright++;
			}
			return t;
		}
}


/* function to delete a leaf */
int deleteoneel(ref node t)

	requires t::pq<n, mx> & n > 0
	ensures t'::pq<n-1, mx2> & 0 <= res <= mx & mx2 <= mx;

{
	int v;

	if (t.nleft == 0)
	{
		v = t.val; 
		t = null;
		return v;
	}
	else 
	{
		int tmp;

		bind t to (tval, tnleft, tnright, tleft, tright) in {
			tmp = deleteone(tnleft, tnright, tleft, tright);
		}

		return tmp;
	}

}

/* function to delete one element */
int deleteone(ref int n1, ref int  n2, ref node l, ref node r)

	requires l::pq<n1, mx1> * r::pq<n2, mx2> & n1 + n2 > 0 & 0 <= n1 - n2 <=1
	ensures l'::pq<n3, mx3> * r'::pq<n4, mx4> & n3 + n4 + 1 = n1 + n2 & 0 <= n3 - n4 <= 1 & 
		n1' = n3 & n2' = n4 & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
{
	if (n1 > n2)
	{
		n1 = n1 - 1;
		return deleteoneel(l);
	}
	else 
	{
		n2 = n2 - 1;
		return deleteoneel(r);
	}
}

/* function to restore the heap property */
void ripple(ref int d, int v, int n1, int n2, node l, node r)

	requires l::pq<n1, mx1> * r::pq<n2, mx2> & 0 <= n1 - n2 <= 1 & d >= mx1, mx2 & 0 <= v <= d
	ensures l::pq<n1, mx3> * r::pq<n2, mx4> & mx3 <= mx1 & mx4 <= mx2 & 
			max1 = max(mx1, v) & max2 = max(mx2, max1) & 
			d' <= max2 & d' >= mx3, mx4, 0;


{
	if (n1 == 0)
	{
		// parent node is leaf, just store v there
		d = v;
	}
	else
	{
		if (n2 == 0)
		{
		// left child is sole child
			if (v >= l.val)
				d = v;
			else
			{
				d = l.val;
				l.val = v;
			}
		}
		else 
		{
			if (l.val >= r.val)
			{
				if (v >= l.val)
					d = v;
				else 
				{
					d = l.val;
					ripple(l.val, v, l.nleft, l.nright, l.left, l.right);
				}
			}
			else
			{
				if (v >= r.val)
					d = v;
				else
				{

					d = r.val;
					ripple(r.val, v, r.nleft, r.nright, r.left, r.right);
				}
			}
		}
	}
}

/* function to delete the root of a heap tree */
int deletemax(ref node t)
	
	requires t::pq<n, mx> & t != null
	ensures t'::pq<n-1, mx2> & mx2 <= res = mx;

{
	int v, tmp;

	tmp  = t.val;

	if (t.nleft == 0)
	{
		t = null;
	}
	else
	{
		bind t to (tval, tnleft, tnright, tleft, tright) in {
			v = deleteone(tnleft, tnright, tleft, tright);
			ripple(tval, v, tnleft, tnright, tleft, tright);
		}
	}

	return tmp;
}
