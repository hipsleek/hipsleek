/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

/* view for a heap tree with positive integers */

pq<n, mx> == self = null & n = 0 & mx = 0
	or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
	& n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) //0 <= n1 - n2 & n1 - n2 <= 1
	inv n >= 0 & mx >= 0;

/*pq1<n, S> == self = null & n = 0 & S = {} 
	or self::node<d, m1, m2, l, r> * l::pq1<n1, S1> * r::pq1<n2, S2> 
	& n = n1 + n2 + 1 & d >= 0 &  m1 = n1 & m2 = n2 & 0 <= n1 - n2 & n1 - n2 <= 1 
	& forall(a : (a notin S1 | a <= d)) & forall(b : (b notin S2 | b <= d)) & S = union(S1, S2, {d})
	inv n >= 0;*/


/* function to insert an element in a priority queue */
//relation INS(int a, int b, int c).
node insert(node t, int v)
//  infer[INS]
  requires t::pq<n, mx> & v >= 0
  ensures res::pq<n1, ma> & n1 = n+1 & (v>=mx & ma = v | ma = mx);//INS(v,mx,ma);//(v>=mx & ma = v | ma = mx);v>=0 & ma>=v & mx>=0
{
	node tmp, tmp_null = null;
	int tmpv;

	if (t == null){
      assume(ma = max(v, mx));
      return new node(v, 0, 0, tmp_null, tmp_null);
    }
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

int deleteoneel1(ref node t)
//infer[res,mx,mx2]
  requires t::pq<n, mx> & n > 0
  ensures t'::pq<n-1, mx2> & mx2 <= mx & 0 <= res <= mx ;//'

/* function to delete a leaf */
int deleteoneel(ref node t)
  //infer[res,mx,mx2]
  requires t::pq<n, mx> & n > 0
  //ensures t'::pq<n-1, mx2> ;//& mx2 <= mx & 0 <= res <= mx &
	ensures t'::pq<m, mx2> & 0 <= res & res <= mx & m = n-1 & mx2 <= mx;//'

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

}
int deleteone1(ref int m1, ref int  m2, ref node l, ref node r)
  requires l::pq<m1, mx1> * r::pq<m2, mx2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq<m1', mx3> * r'::pq<m2', mx4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 
  & m1' = n3 & m2' = n4 & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;//'

/* function to delete one element*/
//can not reverify
int deleteone(ref int m1, ref int  m2, ref node l, ref node r)
//infer[mx1,mx2,mx3,mx4]
     requires l::pq<m1, mx1> * r::pq<m2, mx2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
     ensures l'::pq<m1', mx3> * r'::pq<m2', mx4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 &
     m1' = n3 & m2' = n4 & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
                          //& mx3 <= mx1 & mx4 <= mx2;
  /* 
    requires l::pq<m1, mx1> * r::pq<m2, mx2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
	ensures l'::pq<n3, mx3> * r'::pq<n4, mx4> & n3 + n4 + 1 = m1 + m2 & 0 <= n3 - n4 <= 1 & 
		m1' = n3 & m2' = n4 & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
    */
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
}

/* function to restore the heap property */
//relation RIP(int a, int b, int c).
void ripple(ref int d, int v, int m1, int m2, node l, node r)
//infer[RIP]
  requires l::pq<m1, mx1> * r::pq<m2, mx2> & 0 <= m1 - m2 <= 1 & d >= mx1, mx2 & 0 <= v <= d
  ensures l::pq<m1, mx3> * r::pq<m2, mx4> & mx3 <= mx1 & mx4 <= mx2 &// & RIP(mx1,mx2,d)
	max1 = max(mx1, v) & max2 = max(mx2, max1) &
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
                    //dprint;
					d = r.val;
					ripple(r.val, v, r.nleft, r.nright, r.left, r.right);
				}
			}
		}
	}
}

/* function to delete the root of a heap tree */
//relation DELM(int a, int b, int c).
int deletemax(ref node t)
//infer[DELM]
  requires t::pq<n, mx> & n > 0
  ensures t'::pq<n-1, mx2> & mx2>=0 & res>=mx2 & mx>=res;//& mx2 <= res <= mx;//' DELM(mx,mx2,res)
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
        //dprint;
        tmp = tval;
        ripple(tval, v, tnleft, tnright, tleft, tright);
      }
      return tmp;
	}
}
