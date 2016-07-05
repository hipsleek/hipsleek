/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

/* view for a heap tree with positive integers 
pq<n, mx> == self = null & n = 0 & mx = 0 
	or self::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>& 0 <= m1 - m2 <= 1 & d >= mx1, mx2 & 0 
	   & n = 1 + m1 + m2 & d >= 0, mx1, mx2 & mx >= d & 0 <= m1 - m2 <= 1
	inv n >= 0 & mx >= 0;
*/

pq<n, mx, s> == self = null & n = 0 & mx = 0 & s = 0 
	or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1, s1> * r::pq<m2, mx2, s2>
	& n = 1 + m1 + m2 & m3 = m1-m2 & m3 >= 0 & m3 <= 1 //0 <= n1 - n2 & n1 - n2 <= 1
	& d >= 0 &  ($ d) >= mx1 & ($ d) >= mx2 & mx >= ($ d)
	& s = s1 + s2 + ($ d)) 
	inv n >= 0 & mx >= 0 & s >= 0;


/*pq1<n, S> == self = null & n = 0 & S = {} 
	or self::node<d, m1, m2, l, r> * l::pq1<n1, S1> * r::pq1<n2, S2> 
	& n = n1 + n2 + 1 & d >= 0 &  m1 = n1 & m2 = n2 & 0 <= n1 - n2 & n1 - n2 <= 1 
	& forall(a : (a notin S1 | a <= d)) & forall(b : (b notin S2 | b <= d)) & S = union(S1, S2, {d})
	inv n >= 0;*/


/* function to insert an element in a priority queue */
node insert(node t, int v)

	requires t::pq<n, mx, s> & v >= 0
	ensures res::pq<n1, ma, s1> 
	& n1 = n+1 
	& (v>=mx & ma = v | ma = mx) /*ma = max(v, mx);*/
	& s1 = s + v;
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

/*node insert1(node t, int v)
	requires t::pq1<n, S> & v >= 0
	ensures res::pq1<n1, S1> & n1 = n+1 & S1 = union(S, {v});

{
	node tmp, tmp_null = null; 
	int tmpv;
	
	if (t == null)
		return new node(v, 0, 0, null, null);
	else
		if (v > t.val)
		{
			if (t.nleft <= t.nright)
			{
				tmp = t.left;
				tmpv = t.val;
				t.left = insert1(tmp, tmpv);
				tmpv = t.nleft;
				t.nleft = tmpv + 1;
			}
			else 
			{
				tmp = t.right;
				tmpv = t.val;
				t.right = insert1(tmp, tmpv);
				tmpv = t.nright;
				t.nright = tmpv + 1;
			}
			t.val = v;
			return t;
		}
		else {
			if (t.nleft <= t.nright)
			{
				tmp = t.left;
				t.left = insert1(tmp, v);
				tmpv = t.nleft;
				t.nleft = tmpv + 1;
			}
			else 
			{
				tmp = t.right;
				t.right = insert1(tmp, v);
				tmpv = t.nright;
				t.nright = tmpv + 1;
			}
			return t;
		}
}*/


/* function to delete a leaf */
int deleteoneel(ref node t)

	requires t::pq<n, mx, s> & n > 0
	ensures t'::pq<n-1, mx2, s1> & 0 <= res <= mx & mx2 <= mx & s = s1 + res;
	//ensures t'::pq<m, mx2> & 0 <= res & res <= mx & m = n-1 & mx2 <= mx;

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

/*int deleteoneel1(ref node t)
	requires t::pq1<n, S1> & n > 0
	ensures t'::pq1<n-1, S2> & S1 = union(S2, {res});
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
			tmp = deleteone1(tnleft, tnright, tleft, tright);
		}

		return tmp;
	}

}*/


/* function to delete one element */
int deleteone(ref int m1, ref int  m2, ref node l, ref node r)

	requires l::pq<m1, mx1, s1> * r::pq<m2, mx2, s2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
	ensures l'::pq<m1', mx3, s3> * r'::pq<m2', mx4, s4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 
		& mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi & s1+s2 = s3+s4+res;
  /*  
    requires l::pq<m1, mx1> * r::pq<m2, mx2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
	ensures l'::pq<n3, mx3> * r'::pq<n4, mx4> & n3 + n4 + 1 = m1 + m2 & 0 <= n3 - n4 <= 1 & 
		m1' = n3 & m2' = n4 & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
    */
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


/*int deleteone1(ref int m1, ref int  m2, ref node l, ref node r)

	requires l::pq1<m1, S1> * r::pq1<m2, S2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
	ensures l'::pq1<n3, S3> * r'::pq1<n4, S4> & n3 + n4 + 1 = m1 + m2 & 0 <= n3 - n4 <= 1 & 
		m1' = n3 & m2' = n4 & (S1 = union(S3, {res}) & S2=S4 | S2 = union(S4, {res}) & S1=S3);
{
	if (m1 > m2)
	{
		m1 = m1 - 1;
		return deleteoneel1(l);
	}
	else 
	{
		m2 = m2 - 1;
		return deleteoneel1(r);
	}
}*/

/* function to restore the heap property */
void ripple(ref int d, int v, int m1, int m2, node l, node r)

	requires l::pq<m1, mx1, s1> * r::pq<m2, mx2, s2> & 0 <= m1 - m2 <= 1 & d >= mx1, mx2 & 0 <= v <= d
	ensures l::pq<m1, mx3, s3> * r::pq<m2, mx4, s4> & mx3 <= mx1 & mx4 <= mx2 & 
	max1 = max(mx1, v) & max2 = max(mx2, max1) & s1+s2+v = s3+s4+d' &  
		d' <= max2 & d' >= mx3, mx4, 0;


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
          
			if (v >= l.val)
				d = v;
			else
			{
				//assume false;
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
                  {   assume false;
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


/*void ripple1(ref int d, int v, int m1, int m2, node l, node r)
	requires l::pq1<m1, S1> * r::pq1<m2, S2> & 0 <= m1 - m2 <= 1 & forall (a: (a notin S1 & a notin S2 | a <= d)) & 0 <= v <= d
	ensures l::pq1<m1, S3> * r::pq1<m2, S4> 
	/*& (S1 = S2 | S1 = union(S3, {v})) & (S2 = S4 | S2 = union(S4, {v}))*/
	& exists (b: (b in S2 | b in S1 | b=v & d' <= b)) 
	& d' >= 0  & forall(c: (c notin S3 & c notin S4 | c <= d'));
{
	if (m1 == 0)
	{
		if (m2 == 0)
		{
			d = v;
		}
	}
	else
	{
		if (m2 == 0)
		{
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
					ripple1(l.val, v, l.nleft, l.nright, l.left, l.right);
				}
			}
			else
			{
				if (v >= r.val)
					d = v;
				else
				{

					d = r.val;
					ripple1(r.val, v, r.nleft, r.nright, r.left, r.right);
				}
			}
		}
	}
}*/


/* function to delete the root of a heap tree */
int deletemax(ref node t)
	
	requires t::pq<n, mx, s> & n > 0 
	ensures t'::pq<n-1, mx2, s1> & mx2 <= res <= mx & s = s1 + res;

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
		//assume false;
		bind t to (tval, tnleft, tnright, tleft, tright) in {
			v = deleteone(tnleft, tnright, tleft, tright);
			dprint;
			tmp = tval;
			ripple(tval, v, tnleft, tnright, tleft, tright);
		}
		return tmp;
	}
	
}

/*int deletemax1(ref node t)
	requires t::pq1<n, S> & n > 0 & S != {}
	ensures t'::pq1<n1, S1> & n1 = n-1 & forall(a: (a notin S | a <= res));// & S = union(S1, {res});

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
			v = deleteone1(tnleft, tnright, tleft, tright);
			tmp = tval;
			ripple1(tval, v, tnleft, tnright, tleft, tright);
		}
		return tmp;
	}
	
}*/
