/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

pq<n, mx, S> == self = null & n = 0 & mx = 0 & S = {} 
	or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1, S1> * r::pq<m2, mx2, S2>
	& n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1 //0 <= n1 - n2 & n1 - n2 <= 1
	& S = union({d}, S1, S2))
	inv n >= 0 & mx >= 0 & forall(x: (x notin S | x >= 0));

/* function to insert an element in a priority queue */
node insert(node t, int v)

	requires t::pq<n, mx, S> & v >= 0
	ensures res::pq<n1, ma, S1> & n1 = n+1 & /*ma = max(v, mx);*/ (v>=mx & ma = v | ma = mx) & S1 = union(S, {v});
{
	node tmp, tmp_null = null; 
	int tmpv;

	if (t == null)
		return new node(v, 0, 0, tmp_null, tmp_null);
	else
		if (v > t.val)
		{
			if (t.nleft <= t.nright)
			{
				tmp = t.left;
				tmpv = t.val;
				t.left = insert(tmp, tmpv);
				tmpv = t.nleft;
				t.nleft = tmpv + 1;
			}
			else 
			{
				tmp = t.right;
				tmpv = t.val;
				t.right = insert(tmp, tmpv);
				tmpv = t.nright;
				t.nright = tmpv + 1;
			}
			t.val = v;
			return t;
		}
		else
		{
			if (t.nleft <= t.nright)
			{
				tmp = t.left;
				t.left = insert(tmp, v);
				tmpv = t.nleft;
				t.nleft = tmpv + 1;
			}
			else 
			{
				tmp = t.right;
				t.right = insert(tmp, v);
				tmpv = t.nright;
				t.nright = tmpv + 1;
			}
			return t;
		}
}

//MONA ERROR
/* function to delete a leaf */
int deleteoneel(ref node t)
/*
	requires t::pq<n, mx, S1> & n > 0
	ensures t'::pq<n-1, mx2, S2> & 0 <= res <= mx & mx2 <= mx & S1 = union(S2, {res});
*/
	requires t::pq<n, mx, _> & n > 0
	ensures t'::pq<n-1, mx2, _> & 0 <= res <= mx & mx2 <= mx;
{
	int v;

	if ((t.nleft == 0) && (t.nright == 0))
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
int deleteone(ref int m1, ref int  m2, ref node l, ref node r)

	requires l::pq<m1, mx1, S1> * r::pq<m2, mx2, S2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
	ensures l'::pq<m1', mx3, S3> * r'::pq<m2', mx4, S4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 
		& mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi
		& (S1 = union(S3, {res}) & S2=S4 | S2 = union(S4, {res}) & S1=S3);

{
	if (m1 > m2)
	{
		m1 = m1 - 1;
		return deleteoneel(l);
	}
	else 
	{
		m2 = m2 - 1;
		return deleteoneel(r);
	}
}

//MONA ERROR
/* function to restore the heap property */
void ripple(ref int d, int v, int m1, int m2, node l, node r)
/*
	requires l::pq<m1, mx1, S1> * r::pq<m2, mx2, S2> & 0 <= m1 - m2 <= 1 & d >= mx1, mx2 & 0 <= v <= d & forall (a: (a notin S1 & a notin S2 | a <= d))
	ensures l::pq<m1, mx3, S3> * r::pq<m2, mx4, S4> & mx3 <= mx1 & mx4 <= mx2 
	& (S1 = S3 | S1 = union(S3, {v})) & (S2 = S4 | S2 = union(S4, {v}))
	& max1 = max(mx1, v) & max2 = max(mx2, max1) & d' <= max2 & d' >= mx3, mx4, 0;
*/
	requires l::pq<m1, mx1, _> * r::pq<m2, mx2, _> & 0 <= m1 - m2 <= 1 & d >= mx1, mx2 & 0 <= v <= d 
	ensures l::pq<m1, mx3, _> * r::pq<m2, mx4, _> & mx3 <= mx1 & mx4 <= mx2 
	& max1 = max(mx1, v) & max2 = max(mx2, max1) & d' <= max2 & d' >= mx3, mx4, 0;
{
	if (m1 == 0)
      { //assume false;
		if (m2 == 0)
		{
			d = v;
		}
	}
	else
	{
		if (m2 == 0)
		{
          //assume false;
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
                  {   //assume false;
					d = l.val;
					ripple(l.val, v, l.nleft, l.nright, l.left, l.right);
				}
			}
			else
			{
				if (v >= r.val)
					d = v;
				else
                  {  //assume false;
                    dprint;
					d = r.val;
					ripple(r.val, v, r.nleft, r.nright, r.left, r.right);
				}
			}
		}
	}
}

/* function to delete the root of a heap tree */
int deletemax(ref node t)
/*	
	requires t::pq<n, mx, S> & n > 0 
	ensures t'::pq<n-1, mx2, S1> & mx2 <= res <= mx & forall(a: (a notin S | a <= res));
*/
	requires t::pq<n, mx, _> & n > 0 
	ensures t'::pq<n-1, mx2, _> & mx2 <= res <= mx;
{
	int v, tmp;

	if ((t.nleft == 0) && (t.nright == 0))
	{
		tmp  = t.val;
		t = null;
		return tmp;
	}
	else
	{
		bind t to (tval, tnleft, tnright, tleft, tright) in {
			v = deleteone(tnleft, tnright, tleft, tright);
			dprint;
			tmp = tval;
      
			ripple(tval, v, tnleft, tnright, tleft, tright);
		}
		return tmp;
	}
}
