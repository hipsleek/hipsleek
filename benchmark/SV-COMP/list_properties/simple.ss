/*
 * Simple example: build a list with only 1s and finally a 0 (arbitrary length);
 * afterwards, go through it and check if the list does have the correct form, and in particular
 * finishes by a 0.
 */
data node {
  int val;
  node next;
}

lseg<p, n, S> == self=p & n=0 & S={}
  or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v});

void exit() requires true ensures true;

node create(ref node x, int n)
  requires x::node<0,null> & n >= 0
//  ensures x'::lseg<r, n+1, S> * r::node<0,null> & forall (b : (b notin S | b=1));
  ensures res::lseg<x', n+1, S> * x'::node<0,null> & forall (b : (b notin S | b=1));
{  
  x.val = 1;
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
        node tmp = create(xnext,n-1);
        node y = x;
        x = xnext;
        return y;
      }
    }
  }
}

node main(int m)
  requires m > 0
  ensures res::lseg<r, m+1, S> * r::node<0,null> & forall (b : (b notin S | b=1));
  //ensures res::node<0,null>;
{
  node a = new node(0,null);
  if (a==null) {
    exit();
    return a;
  }
  else
  {
    node x = a;
    a = create(x,m);
    return a;
    //return x;
  }
}


