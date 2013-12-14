data node{
	int val;
	node next;
}

inflist<n> == self = null & n = 0
	or self::node<_,q> * q::inflist<n-1> 
inv n >= 0;

node take(node x, int k)
  requires x::inflist<\inf>
  ensures  res::inflist<k> * x::inflist<\inf> ;
{
  node y;
  if (k == 0) return null;
  else {
    y = new node(x.val, null);
    y.next = take (x.next, k-1);
    return y;
  }
}

inflistB<n,B> == self = null & n = 0 & B={}
  or self::node<v,q> * q::inflistB<n-1,B1> & B = union({v},B1) 
inv n >= 0;

node takeB(node x, int k)
  requires x::inflistB<\inf,B>
  ensures  res::inflistB<k,Bres> * x::inflistB<\inf,B> & Bres subset B;
{
  node y;
  if (k == 0) return null;
  else {
    y = new node(x.val, null);
    y.next = takeB (x.next, k-1);
    return y;
  }
}

/* node takekB(node x, int k) */
/*   requires x::inflistB<n,B> */
/*   ensures  res::inflistB<k,Bres> * x::inflistB<n,B> & Bres subset B; */
/* { */
/*   node y; */
/*   if (x == null) return null; */
/*   else  */
/*     if (k == 0) return null; */
/*     else { */
/*       y = new node(x.val, null); */
/*       y.next = take (x.next, k-1); */
/*       return y; */
/*     } */
/* } */