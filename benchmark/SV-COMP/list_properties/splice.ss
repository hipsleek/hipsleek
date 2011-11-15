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
  or self::node<v, r> * r::lseg<p, n-1, S1> & S=union(S1, {v})
  inv n>=0;

ll<S> == self=null & S={}
  or self::node<v, r> * r::ll<S1> & S=union(S1, {v});

void exit() requires true ensures true;

node create(ref node x, int n, int flag)
  requires x::node<0,null> & n >= 0
  ensures res::lseg<x', n+1, S> * x'::node<0,null> & forall (b : (b notin S | b=1 | b=2));
  //ensures x'::node<0,null>;
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
        node tmp = create(xnext,n-1,flag);;
        node y = x;
        x = xnext;
        return y;
      }      
    }
  }
}
/*
void part(ref node x, ref node l1, ref node l2, int flag)
  requires x::node<3,null>  
  ensures x'::node<3,null>;  
  requires x::node<2,xb> * xb::lseg<t0b,m0b,S0b> * t0b::node<3,null>
  * l2::lseg<t2,m2,S2> * t2::node<0,null>
  & flag=0
  & forall (ab : (ab notin S0b | ab=1 | ab=2))
  & forall (c : (c notin S2 | c=2))
  ensures x'::node<1,x1b> * x1b::lseg<r0b,m0b-1,T0b> * r0b::node<3,null>  
  * l2'::lseg<r2,1+m2,T2> * r2::node<0,null> 
  & flag=1 & S0b=union(T0b,{2},{1}) & T2=union(S2,{2})
  & forall (a1b : (a1b notin T0b | a1b=1 | a1b=2))
  & forall (c1 : (c1 notin T2 | c1=2));
  requires x::node<1,xa> * xa::lseg<t0a,m0a,S0a> * t0a::node<3,null>
  * l1::lseg<t1,m1,S1> * t1::node<0,null>
  & flag=1
  & forall (aa : (aa notin S0a | aa=1 | aa=2))
  & forall (b : (b notin S1 | b=1))
  ensures x'::node<2,x1a> * x1a::lseg<r0a,m0a-1,T0a> * r0a::node<3,null>  
  * l1'::lseg<r1,1+m1,T1> * r1::node<0,null> 
  & flag=0 & S0a=union(T0a,{1},{2}) & T1=union(S1,{1})
  & forall (a1a : (a1a notin T0a | a1a=1 | a1a=2))
  & forall (b1 : (b1 notin T1 | b1=1));
{  
  if (x.val==3) return;
  else {    
    if (flag==1) {
      node t = x;
      x = x.next;
      t.next = l1;
      l1 = t;
      flag = 0;
    }
    else {
      node t = x;
      x = x.next;
      t.next = l2;
      l2 = t;
      flag = 1;
    }
    part(x,l1,l2,flag);
    return;
  }
}
*/

void part(ref node x, ref node l1, ref node l2, int flag)
  requires x::lseg<r,_,S> * r::node<3,null> & forall (a : (a notin S | a=1 | a=2))
  ensures x'::node<3,null>; //* l1'::ll<S1> * l2'::ll<S2> 
  //& forall (b : (b notin S1 | b=1)) & forall (c : (c notin S2 | c=2));
{  
  if (x.val==3) return;
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
    part(x,l1,l2,flag);
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
    a = create(x,m,flag);
    x.val = 3;
    if (a.val==3) return a;
    else {
      flag = 1;
      node l1;
      node l2;
      x = a;
      part(x,l1,l2,flag);
      return x;
    }
  }
}

