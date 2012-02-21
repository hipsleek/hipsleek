data node {
	int val;
	node next;
}

ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});

/* return the tail of a singly linked list */
relation GN(bag a, bag b, bag c).
node get_next(ref node x)
  infer[GN]
  requires x::ll2<n,S> & x!=null
  ensures x'::ll2<1,S1> * res::ll2<n-1,S2> & GN(S,S1,S2);//S  = union(S1, S2)//'
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

//fail to compute FGE
relation FGE(bag a, int b).
node find_ge(node x, int v)
  infer[FGE]
  requires x::ll2<n,S> & n >= 0
/* case {
  n=0 -> ensures res=null;
  n!=0 -> ensures res::node<m,_> & m > v & m in S;
  }*/
  ensures res = null  or res::node<m,_> & m > v & FGE(S,m);//m in S;//FGE(S,m);//m in S;
{
  if(x == null)
    return null;
  else {
    if(x.val > v)
      return x;
    else
      return find_ge(x.next, v);
  }
}
