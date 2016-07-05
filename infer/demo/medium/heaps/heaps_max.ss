/* Priority Queues */
/* Given Shape + Size -> Infer Max Element Property */

data node3 {
  int val;
  int nleft;
  int nright;
  node3 left;
  node3 right;
}

pqN<n> == self = null & n = 0
  or (exists m3: self::node3<d, m1, m2, l, r> * l::pqN<m1> * r::pqN<m2>
                 & n=1+m1+m2 & d>=0 & m3=m1-m2 & m3>=0 & m3<=1);

/************************************************************/


/* Insert an element into a priority queue */
node3 insert(node3 t, int v)
  requires t::pqN<n> & v >= 0
  ensures res::pqN<m> & m=n+1;
{
  node3 tmp = null;
  int tmpval;

  if (t == null)
    return new node3(v, 0, 0, null, null);
  else
    if (v > t.val)
    {
      if (t.nleft <= t.nright)
      {
        tmp = t.left;
        tmpval = t.val;
        t.left = insert(tmp, tmpval);
        tmpval = t.nleft;
        t.nleft = tmpval + 1;
      }
      else 
      {
        tmp = t.right;
        tmpval = t.val;
        t.right = insert(tmp, tmpval);
        tmpval = t.nright;
        t.nright = tmpval + 1;
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
        tmpval = t.nleft;
        t.nleft = tmpval + 1;
      }
      else 
      {
        tmp = t.right;
        t.right = insert(tmp, v);
        tmpval = t.nright;
        t.nright = tmpval + 1;
      }
      return t;
    }
}

/* Delete a leaf */
int deleteoneel(ref node3 t)
  requires t::pqN<n> & n>0
  ensures t'::pqN<n-1> & res>=0;
{
  if ((t.nleft == 0) && (t.nright == 0))
  {
    int v;
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

int deleteone(ref int m1, ref int m2, ref node3 l, ref node3 r)
  requires l::pqN<m1> * r::pqN<m2> & m1+m2>0 & 0<=m1-m2<=1
  ensures l'::pqN<m1'> * r'::pqN<m2'> & m1'+m2'+1=m1+m2 & 0<=m1'-m2'<= 1 & res>=0;
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

/* Restore the heap property */
void ripple(ref int d, int v, int m1, int m2, node3 l, node3 r)
  requires l::pqN<m1> * r::pqN<m2> & 0<=v<=d & 0<=m1-m2<=1
  ensures l::pqN<m1> * r::pqN<m2> & d'>=0;
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
        {
          d = v;
        }
        else 
        {  
          d = l.val;
          ripple(l.val, v, l.nleft, l.nright, l.left, l.right);
        }
      }
      else
      {
        if (v >= r.val)
        {
          d = v;
        }
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
int deletemax(ref node3 t)
  requires t::pqN<n> & n>0
  ensures t'::pqN<m> & m=n-1;

{
  int v, tmp;

  if ((t.nleft == 0) && (t.nright == 0))
  {
    tmp = t.val;
    t = null;
    return tmp;
  }
  else
  {
    bind t to (tval, tnleft, tnright, tleft, tright) in {
      v = deleteone(tnleft, tnright, tleft, tright);
      tmp = tval;
      ripple(tval, v, tnleft, tnright, tleft, tright);
    }
    return tmp;
  }
}
