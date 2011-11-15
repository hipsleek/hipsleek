/*
 * Simple example: build a list with only 1s, then 2s and finally
 * on 3 (arbitrary length); afterwards, go through it and check
 * if the the list does have the correct form, and in particular
 * finishes by a 3.
 */
data node {
  int val;
  node next;
}

lseg<p, n, S> == self=p & n=0 & S={}
  or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v});

void exit() requires true ensures true;

node create(ref node x, int n, int v)
  requires x::node<0,null> & n >= 0
  ensures res::lseg<r, n+1, S> * x'::node<0,null> & forall (b : (b notin S | b=v));
  //ensures x'::node<0,null>;
{
  x.val = v;
  node t = new node(0,null);
  if (t==null) {
    exit();
    return x;
  }
  else
  {
    x.next = t;    
    if (n==0)
    {
      node y = x;
      x = x.next;
      return y;
    }
    else
    {
      bind x to (xval,xnext) in {
        node tmp = create(xnext,n-1,v);
        node y = x;
        x = xnext;
        return y;      
      }
    }
  }
}

node main(int m)
  requires m > 0
  //ensures res::lseg<r1, m+1, S1> * r1::lseg<r2, m+1, S2> * r2::node<3,null>;
  //& forall (b : (b notin S1 | b=1)) & forall (c : (c notin S2 | c=2));
  ensures res::node<3,null>;
{
  node a = new node(0,null);
  if (a==null) {
    exit();
    return a;
  }
  else
  {
    node x = a;
    a = create(x,m,1);
    node tmp = create(x,m,2);
    x.val = 3;
    return x;
    //return a;
  }
}


