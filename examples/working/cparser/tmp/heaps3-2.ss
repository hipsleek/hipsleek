/* priority queues */

data node {
  int val;
  int nleft;
  int nright;
  node__star left;
  node__star right;
}

data node__star {
  node pdata;
}

data node__star__star {
  node__star pdata;
}


data int__star {
  int pdata;
}

pq<n, mx> == self = null & n = 0 & mx = 0 
  or (exists m3: self::node__star<p> * p::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
  & n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) //0 <= n1 - n2 & n1 - n2 <= 1
  inv n >= 0 & mx >= 0;


/* function to delete a leaf */
int deleteoneel(node__star__star t)
  requires t::node__star__star<t1> * t1::pq<n, mx> & n > 0
  ensures t::node__star__star<t2> * t2::pq<n-1, mx2> & 0 <= res <= mx & mx2 <= mx;
{
  int v;

  if ((t.pdata.pdata.nleft == 0) && (t.pdata.pdata.nright == 0))
  {
    v = t.pdata.pdata.val; 
    t.pdata = null;
    return v;
  }
  else 
  {
    int tmp;

/*
    bind t to (v) in {
      bind v to (tval, tnleft, tnright, tleft, tright) in {
        int__star ttnleft = new int__star(tnleft);
        int__star ttnright = new int__star(tnright);
        tmp = deleteone(ttnleft, ttnright, tleft, tright);
      }
    }

    bind t to (tval, tnleft, tnright, tleft, tright) in {
      tmp = deleteone(tnleft, tnright, tleft, tright);
    }
*/

    int__star tnleft = new int__star(t.pdata.pdata.nleft);
    int__star tnright = new int__star(t.pdata.pdata.nright);
    node__star__star tleft = new node__star__star(t.pdata.pdata.left);
    node__star__star tright = new node__star__star(t.pdata.pdata.right);
    
    tmp = deleteone(tnleft, tnright, tleft, tleft);
    
    t.pdata.pdata.nleft = tnleft.pdata;
    t.pdata.pdata.nright = tnright.pdata;
    t.pdata.pdata.left = tleft.pdata;
    t.pdata.pdata.right = tright.pdata;

    return tmp;
  }

}


/* function to delete one element */
int deleteone(int__star m1, int__star m2, node__star__star l, node__star__star r)
  requires m1::int__star<im1> * m2::int__star<im2> * l::node__star__star<l1> * l1::pq<im1, mx1> * r::node__star__star<r1> * r1::pq<im2, mx2> & im1 + im2 > 0 & 0 <= im1 - im2 <=1
  ensures m1::int__star<am1> * m2::int__star<am2> * l::node__star__star<l2> * l2::pq<am1, mx3> * r::node__star__star<r2> * r2::pq<am2, mx4> & am1 + am2 + 1 = im1 + im2 & 0 <= am1 - am2 <= 1 
    & mx3 <= mx1 & mx4 <= mx2 & maxi = max(mx1, mx2) & 0 <= res <= maxi;
{
  if (m1.pdata > m2.pdata)
  {
    m1.pdata = m1.pdata - 1;
    return deleteoneel(l);
  }
  else 
  {
    m2.pdata = m2.pdata - 1;
    return deleteoneel(r);
  }
}

