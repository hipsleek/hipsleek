data node {
  int val;
  int height;
  node left;
  node right;
}

tree<> == self=null
  or self::node<_,h,l,r> * l::tree<> * r::tree<> & h>=0
  inv true;

int height(node x)
  infer [@post_n]
  requires x::tree<>
  ensures x::tree<>;
{
  if (x==null)
    return 0;
  else
    return x.height;
}
