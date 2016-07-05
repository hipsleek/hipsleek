data node {
 int val;
 node next;
}

HeapPred H(node x, int v). // non-ptrs are @NI by default
PostPred G(node x, int v). // non-ptrs are @NI by default

  ll<n:int> == self=null & n=0
  or self::node<v,q>*q::ll<n-1>& self!=null
 inv true;

node create_list(int m)
  infer [G]  requires true  ensures G(res,m);
//  requires true ensures res::ll<m>;
{
  if (m==0) return null;
  else {
    node tmp = create_list(m-1);
    return new node(0,tmp);
  }
}
