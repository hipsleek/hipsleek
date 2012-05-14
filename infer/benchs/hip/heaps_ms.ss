/* priority queues */
//this file is OK. change with care
//shape --> memory + size
data node {
	int val;
	int nleft;
	int nright;
	node left;
	node right;
}

/* view for a heap tree with positive integers */

pq2<n> == self = null & n = 0
	or (exists m3: self::node<d, m1, m2, l, r> * l::pq2<m1> * r::pq2<m2>
	& n = 1 + m1 + m2 & d >= 0 & m3 = m1-m2 & m3 >= 0 & m3 <= 1)
	inv n >= 0;

/* function to insert an element in a priority queue */
relation INS(int a, int b).
node insert(node t, int v)
  infer[t,INS]
  requires t::pq2<n> & v >= 0
  ensures res::pq2<n1> & INS(n1,n);//n1 = n+1;//INS(n1,n)
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
  requires t::pq2<n> & n > 0
  ensures t'::pq2<n-1> & 0 <= res;//'

int deleteoneel(ref node t)
  infer @post [t]
  requires t::pq2<n> //& n > 0 & t!=null
  ensures t'::pq2<n1> ;//'& n1=n-1 & res>=0 ;//'n1=n-1 & res>=0
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
  requires l::pq2<m1> * r::pq2<m2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq2<m1'> * r'::pq2<m2'> & res>=0 & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1;//'

int deleteone(ref int m1, ref int  m2, ref node l, ref node r)
  infer @post [l,r]
  requires l::pq2<m1> * r::pq2<m2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq2<m1'> * r'::pq2<m2'> ;//& res>=0 & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1;//'
//m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1;
//DELONE2(m1,m1',m2,m2') & //m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1
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
void ripple1(ref int d, int v, int m1, int m2, node l, node r)
	requires l::pq2<m1> * r::pq2<m2> & 0 <= d & 0 <= m1 - m2 <= 1
	ensures l::pq2<m1> * r::pq2<m2> & d'>=0;//'

relation RIP(int a).
void ripple(ref int d, int v, int m1, int m2, node l, node r)
  infer [RIP,m1,m2]
  requires l::pq2<m1> * r::pq2<m2> &  0 <= v <= d //& 0 <= m1 - m2 <= 1 //RIP(m1,m2)//& 0 <= m1 - m2 <= 1 & 0 <= v <= d
  ensures l::pq2<m1> * r::pq2<m2>  & RIP(d);//'& d'>=0
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
relation A(int a, int b).
int deletemax(ref node t)
  infer[n,A]
  requires t::pq2<n> //& n > 0 & t!=null
  ensures t'::pq2<n1> & A(n1,n);//'& n1=n-1

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
        ripple1(tval, v, tnleft, tnright, tleft, tright);
      }
      return tmp;
	}
}
