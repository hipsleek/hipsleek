/* priority queues */

data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

/* view for a heap tree with positive integers */

pq1<> == self = null
	or self::node<d, m1, m2, l, r> * l::pq1<> * r::pq1<> & d >= 0
	inv true;


/* function to insert an element in a priority queue */
//relation INS(node a, node b).
node insert(ref node t, int v)
  infer [res,t]
  requires t::pq1<> & v >= 0
  ensures res::pq1<>;//'res!=null res=t
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

/* function to delete a leaf */
int deleteoneel1(ref node t)
  requires t::pq1<> & t!=null
	ensures t'::pq1<> & res>=0;

int deleteoneel(ref node t)
  infer[t,res]
  requires t::pq1<> //& t!=null
	ensures t'::pq1<> ;//& 0 <= res;// <= mx & mx2 <= mx;
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
			tmp = deleteone1(tnleft, tnright, tleft, tright);
		}

		return tmp;
	}

}

/* function to delete one element */
int deleteone1(ref int m1, ref int  m2, ref node l, ref node r)
  requires l::pq1<> * r::pq1<>  & l!=null & r!=null//& m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq1<> * r'::pq1<>  & res>=0 & (m2'+1)>=m2 & m2>=m2' & m2'+m1'+1=m1+m2;

relation DELONE(int a, int b, int c, int d).
int deleteone(ref int m1, ref int  m2, ref node l, ref node r)
  infer[DELONE]
  requires l::pq1<> * r::pq1<> & l!=null & r!=null//& m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq1<> * r'::pq1<> & DELONE(m1,m1',m2,m2') & res>=0;//(m2'+1)>=m2 & m2>=m2' & m2'+m1'+1=m1+m2
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

void ripple1(ref int d, int v, int m1, int m2, node l, node r)
  requires l::pq1<> * r::pq1<> & l!= null & r!=null
  ensures l::pq1<> * r::pq1<> ;//& RIP(d,v,m1,m2);//'

/* function to restore the heap property */
void ripple(ref int d, int v, int m1, int m2, node l, node r)
  requires l::pq1<> * r::pq1<> & l!= null & r!=null
  ensures l::pq1<> * r::pq1<>;
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
int deletemax(ref node t)
  infer[t]
  requires t::pq1<> // & t!=null
  ensures t'::pq1<>;//'

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
        v = deleteone1(tnleft, tnright, t.left, t.right);
			//dprint;
        tmp = tval;
        ripple1(tval, v, tnleft, tnright, t.left, t.right);
      }
		return tmp;
	}
}
