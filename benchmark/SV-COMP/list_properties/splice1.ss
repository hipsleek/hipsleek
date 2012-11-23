/*
 * Odd-Even Splice example: create a list with 1s at odd positions
 * and 2s at even ones. The list is ended by a 3 at the last
 * position.
 * Then, split it into two lists (with only 1s or 2s) and go
 * through those as usual.
 */
data node {
  int val;
  node next;
}

lseg<p, n, S> == self=p & n=0 & S={}
  or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v});

ll<S> == self=null & S={}
  or self::node<v, r> * r::ll<S1> & S=union(S1, {v});

void exit() requires true ensures true;

void create(ref node x, int n, int flag)
  requires x::node<0,null> & n >= 0
  ensures x'::lseg<r, n+1, S> * r::node<0,null>;// & forall (b : (b notin S | b=1 | b=2));
//  ensures x'::node<0,null>;
{
  if (flag==1) {
    x.val = 1;
    flag = 0;
  }
  else {
    x.val = 2;
    flag = 1;
  }
  node t = new node(0,null);
  if (t==null) exit();
  else
  {
    x.next = t;    
    if (n==0)
    {
      return;
    }
    else
    {
      bind x to (xval,xnext) in {
        create(xnext,n-1,flag);
      }
    }
  }
}

void part(ref node l1, ref node l2, ref node x, int flag)
  requires x::lseg<r,_,S> * r::node<3,null> & forall (a : (a notin S | a=1 | a=2))
  ensures x'::node<3,null>;// * l1'::ll<S1> * l2'::ll<S2> & forall (b : (b notin S1 | b=1)) & forall (c : (c notin S2 | c=2));
{  
  if (x.val==3)
    return;
  else {
    node t = x;
    x = x.next;
    if (flag==1) {
      t.next = l1;
      l1 = t;
      flag = 0;
    }
    else {
      t.next = l2;
      l2 = t;
      flag = 1;
    }
    part(l1,l2,x,flag);
    return;
  }
}

node main(int m)
  requires m > 0
  //ensures res::lseg<r, m+1, S> * r::node<3,null> & forall (b : (b notin S | b=1 | b=2));
  ensures res::node<3,null>;
{
  int flag = 1;
  node a = new node(0,null);
  if (a==null) {
    exit();
    return a;
  }
  else
  {
    node x = a;
    create(x,m,flag);
    x.val = 3;
    if (a==null) return a;
    else {
      flag = 1;
      node l1;
      node l2;
      //x = a;
      part(l1,l2,x,flag);
      return x;
      //return a;
    }
  }
}

