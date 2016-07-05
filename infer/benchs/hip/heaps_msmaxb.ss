/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

/* view for a heap tree with positive integers */

/*pq<n, mx> == self = null & n = 0 & mx = 0*/
/*	or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>*/
/*	& n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) //0 <= n1 - n2 & n1 - n2 <= 1*/
/*	inv n >= 0 & mx >= 0;*/

pq1<n, mx,S> == self = null & n = 0 & mx = 0 & S={}
  or (exists m3: self::node<d, m1, m2, l, r> * l::pq1<m1, mx1,S1> * r::pq1<m2, mx2,S2>
	& n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx = d & m3 = m1-m2 & m3 >= 0 & m3 <= 1
      & S=union(S1,S2,{d})) //0 <= n1 - n2 & n1 - n2 <= 1
	inv n >= 0 & mx >= 0;

/* function to insert an element in a priority queue */
relation INS(bag a, bag b).
node insert(node t, int v)
  infer [INS]
  requires t::pq1<n, mx,S1> & v >= 0
  ensures res::pq1<n+1, ma,S2> & (v>=mx & ma = v | ma = mx) & {v} subset S2 & INS(S1,S2);//S2=union(S1,{v});//INS(S1,S2,v);
{
	node tmp, tmp_null = null;
	int tmpv;

	if (t == null){
      assume ma = max(v, mx);
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
  requires t::pq1<n, mx,S1> & n > 0
  ensures t'::pq1<n-1, mx2,S2> & mx2 <= mx & 0 <= res <= mx & S2 subset S1 ;//'

/* function to delete a leaf */
relation DEL(bag a, bag b).
int deleteoneel(ref node t)
// infer[DEL]
  requires t::pq1<n, mx,S1> & n > 0
  ensures t'::pq1<n-1, mx2,S2> & mx2 <= mx & 0 <= res <= mx ;//& DEL(S1,S2);// & S2 subset S1 ;//'
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
  requires l::pq1<m1, mx1,S1> * r::pq1<m2, mx2,S2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq1<m1', mx3,S3> * r'::pq1<m2', mx4,S4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 
  & m1' = n3 & m2' = n4 & mx3 <= mx1 & mx4 <= mx2 &
//maxi = max(mx1, mx2)
  ((maxi=mx1 & maxi >= mx2) | (maxi=mx2 & maxi > mx1))
  & 0 <= res <= maxi & S5=union(S1,S2) & S6=union(S3,S4) & S6 subset S5;//'

/* function to delete one element*/
relation DELONE (bag a, bag b, bag c, bag d).
int deleteone(ref int m1, ref int  m2, ref node l, ref node r)
  infer [DELONE]
  requires l::pq1<m1, mx1,S1> * r::pq1<m2, mx2,S2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq1<m1', mx3,S3> * r'::pq1<m2', mx4,S4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 
  & m1' = n3 & m2' = n4 & mx3 <= mx1 & mx4 <= mx2 &
//maxi = max(mx1, mx2)
  ((maxi=mx1 & maxi >= mx2) | (maxi=mx2 & maxi > mx1))
  & 0 <= res <= maxi & DELONE(S1,S2,S3,S4);//S5=union(S1,S2) & S6=union(S3,S4) & S6 subset S5;//'
/*
S4<subset> S2  & S1=S3 | S3<subset> S1  & S2=S4
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
//relation RIP(bag a, bag b, bag c, bag d).
void ripple(ref int d, int v, int m1, int m2, node l, node r)
//  infer[RIP]
  requires l::pq1<m1, mx1,S1> * r::pq1<m2, mx2,S2> & 0 <= m1 - m2 <= 1 & d >= mx1, mx2 & 0 <= v <= d
  ensures l::pq1<m1, mx3,S3> * r::pq1<m2, mx4,S4>
  & ((max1=mx1 & max1 >= v) | (max1=v & max1 > mx1)) & ((max2=mx2 & max2>= max1) | (max2=max1 & max2 > mx2)) //& RIP(S1,S2,S3,S4)
  & d' <= max2 & d' >= mx3, mx4, 0;
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
relation DELM(int a, int b, int c).
int deletemax(ref node t)
//  infer[DELM]
  requires t::pq1<n, mx,S1> & n > 0
  ensures t'::pq1<n-1, mx2,S2> & mx2 <= res <= mx;//DELM(mx,mx2,res);//& mx2 <= res <= mx;//'mx2>=0 & res>=mx2 & mx>=res
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

