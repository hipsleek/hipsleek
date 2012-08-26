data node {
	int val;
	node next;
}

sll2<n, S, sm, lg> == self = null & n = 0 & sm <= lg & S = {}
  or (exists qs,ql: self::node<qmin, q> * q::sll2<n-1, S1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin
        & S = union(S1, {qmin}))
	inv n >= 0 & sm <= lg;

relation CL(int a, int b, int c).
  node create_list(int n, int v)
  infer[CL]
  requires n>=0
//  ensures res::sll2<n,S, sm, lg> & CL(sm,lg,v);
 case {
  n = 0 -> ensures res=null;
  n > 0 -> ensures res::sll2<n,S,sm, lg> & CL(sm,lg,v);//& sm=v & v=lg;
  n<0 -> ensures false;
}
{
  node tmp;
  if (n == 0) {
    return null;
  }
  else {
    n  = n - 1;
    tmp = create_list(n,v);
    return new node (v, tmp);
  }
}

relation PF(int a, int b, int c, int d).
node pop_front(ref node x)
infer[PF]
  requires x::sll2<m, S1, sm1, lg1> & x!=null//m>=1
  ensures x'::sll2<m-1, S2, sm2, lg2> & PF(sm1,sm2,lg1,lg2);// & sm1<=sm2 & lg2<=lg1;//'
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}
