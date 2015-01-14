relation R(int a, int b, int c).

data node {
  int val;
  node left;
  node right;
}

tree<height> == self=null & height=0
  or self::node<_,l,r> * l::tree<height1> * r::tree<height2> & height=max(height1,height2)+1
  inv height>=0;

int height(node x)
  /* infer [R] */
  infer [@pre_n,@post_n]
  requires x::tree<n>
  ensures x::tree<m>; // & R(n,m,res);
{
  if (x==null) return 0;
  else if (height(x.left) > height(x.right))
    return height(x.left) + 1;
  else
    return height(x.right) + 1;
}
