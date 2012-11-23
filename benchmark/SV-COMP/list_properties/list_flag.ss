/*
 * Variation on example 0: use a (non-deterministic) boolean
 * flag to set the value of the elements in the list before
 * 3 to a value depending on the flag, and check later on
 * that the list is what has been built just before.
 */
data node {
  int val;
  node next;
}

lseg<p, n, S> == self=p & n=0 & S={}
  or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v});

void exit() requires true ensures true;

node create(ref node x, int n, int flag)
  requires x::node<0,null> & n >= 0
  ensures res::lseg<x', n+1, S> * x'::node<0,null> & forall (b : (b notin S | b=1 | b=2));
  //ensures x'::node<0,null>;
{
  if (flag==1) x.val = 1;
  else x.val = 2;
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
        node tmp = create(xnext,n-1,flag);
        node y = x;
        x = xnext;
        return y;
      }
    }
  }
}


node main(int m, int flag)
  requires m > 0
  ensures res::lseg<r, m+1, S> * r::node<3,null> & forall (b : (b notin S | b=1 | b=2));
  //ensures res::node<3,null>;
{
  node a = new node(0,null);
  if (a==null) {
    exit();
    return a;
  }
  else
  {
    node x = a;
    a = create(x,m,flag);    
    x.val = 3;
    //return x;
    return a;
  }
}


