/* priority queues */

data node {
  int val;
  int nleft;
  int nright;
  node left;
  node right;
}


pq<n, mx> == self = null & n = 0 & mx = 0 
  or (exists m3: self::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
  & n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) //0 <= n1 - n2 & n1 - n2 <= 1
  inv n >= 0 & mx >= 0;


/* function to delete a leaf */
int deleteoneel(ref node t)

  requires t::pq<n, mx> & n > 0
  ensures t'::pq<n-1, mx2> & 0 <= res <= mx & mx2 <= mx;
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
/*
    bind t to (tval, tnleft, tnright, tleft, tright) in {
      tmp = deleteone(tnleft, tnright, tleft, tright);
    }
*/

    tmp = deleteone(t.nleft, t.nright, t.left, t.right);
    return tmp;
  }

}


/* function to delete one element */
int deleteone(ref int m1, ref int  m2, ref node l, ref node r)

  requires l::pq<m1, mx1> * r::pq<m2, mx2> & m1 + m2 > 0 & 0 <= m1 - m2 <=1
  ensures l'::pq<m1', mx3> * r'::pq<m2', mx4> & m1' + m2' + 1 = m1 + m2 & 0 <= m1' - m2'<= 1 
    & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
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
