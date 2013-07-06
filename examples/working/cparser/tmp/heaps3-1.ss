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

data int__star {
  int pdata;
}

pq<n, mx> == self = null & n = 0 & mx = 0 
  or (exists m3: self::node__star<p> * p::node<d, m1, m2, l, r> * l::pq<m1, mx1> * r::pq<m2, mx2>
  & n = 1 + m1 + m2 & d >= 0 &  d >= mx1 & d >= mx2 & mx >= d & m3 = m1-m2 & m3 >= 0 & m3 <= 1) //0 <= n1 - n2 & n1 - n2 <= 1
  inv n >= 0 & mx >= 0;


/* function to delete a leaf */
int deleteoneel(node__star t)

  requires t::pq<n, mx> & n > 0
  ensures t'::pq<n-1, mx2> & 0 <= res <= mx & mx2 <= mx;
  //ensures t'::pq<m, mx2> & 0 <= res & res <= mx & m = n-1 & mx2 <= mx;

{
  int v;

  if ((t.pdata.nleft == 0) && (t.pdata.nright == 0))
  {
    v = t.pdata.val; 
    t.data = null;
    return v;
  }
  else 
  {
    int tmp;

    int__star ttnleft;
    int__star ttnright;
    /*
    bind t to k {
      bind k to (tval, tnleft, tnright, tleft, tright) in {
        ttnleft = new int__star(tnleft);
        ttnright = new int__star(tnright);
        tmp = deleteone(ttnleft, ttnright, tleft, tright);
      }
    }
    */
    ttnleft = new int__star(t.pdata.nleft);
    ttnright = new int__star(t.pdata.nleft);
    node__star tleft = t.pdata.left;
    node__star tright = t.pdata.right;
    tmp = deleteone(ttnleft, ttnright, tleft, tright);
    t.pdata.nleft = ttnleft.pdata;
    t.pdata.nright = ttnright.pdata;


//    tmp = deleteone(t.nleft, t.nright, t.left, t.right);
    return tmp;
  }

}


/* function to delete one element */
int deleteone(int__star m1, int__star  m2, ref node__star l, ref node__star r)

  requires m1::int__star<im1> * m2::int__star<im2> * l::pq<im1, mx1> * r::pq<im2, mx2> & im1 + im2 > 0 & 0 <= im1 - im2 <=1
  ensures m1::int__star<am1> * m2::int__star<am2> * l'::pq<am1, mx3> * r'::pq<am2, mx4> & am1 + am2 + 1 = im1 + im2 & 0 <= am1 - am2<= 1 
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
