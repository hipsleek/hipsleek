relation R(int a, int b, int c).

data node {
  int val;
  node left;
  node right;
}

tree<size> == self=null & size=0
  or self::node<_,l,r> * l::tree<size1> * r::tree<size2> & size=size1+size2+1
  inv size>=0;

int size(node x)
  /* infer [R] */
  infer [@pre_n,@post_n]
  requires x::tree<n>
  ensures x::tree<m>; // & R(n,m,res);
{
  if (x==null) return 0;
  else return size(x.left) + size(x.right) + 1;
}
