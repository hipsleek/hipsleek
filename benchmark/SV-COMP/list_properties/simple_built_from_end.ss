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

void create(ref node x, int n)
  requires x::lseg<r,a,S1> * r::node<0,null> & n >= 0 & forall (b : (b notin S1 | b=1))
  ensures x'::lseg<r,n+1+a,S> * r::node<0,null> & forall (c : (c notin S | c=1));  
{
  node t = new node(0,null);
  if (t==null) exit();
  else
  {
    t.val = 1;
    t.next = x;
    x = t;
    if (n==0)
    {
      return;
    }
    else
    {
      create(x,n-1);
    }
  }
}

node main(int m)
  requires m > 0
  ensures res::lseg<r, m+1, S> * r::node<0,null> & forall (b : (b notin S | b=1));  
{
  node x = new node(0,null);
  if (x==null) {
    exit();
    return x;
  }
  else
  {
    create(x,m);
    return x;
  }
}


