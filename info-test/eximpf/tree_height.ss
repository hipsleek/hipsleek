data node {
  int v;
  node l;
  node r;
  node p;
}

pred pub_tree<n,p> == self=null & n=0 & self <E @Lo
  or self::node<v,l,r,p> * l::pub_tree<ln,self> * r::pub_tree<rn,self>
  & n>0 & n=ln+rn+1 & self <E @Lo & v <E @Lo
  inv n>=0;
pred pri_tree<n,p> == self=null & n=0 & self <E @Hi
  or self::node<v,l,r,p> * l::pri_tree<ln,self> * r::pri_tree<rn,self>
  & n>0 & n=ln+rn+1 & self <E @Hi & v <E @Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_tree<n,p> -> self::pri_tree<n,p>;
lemma_safe "private->public_fail" self::pri_tree<n,p> -> self::pub_tree<n,p>;

int height1_safe(node p)
  requires p::pub_tree<n,_> & p <E @Lo
  ensures res=n & res <E @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + height1_safe(p.l) + height1_safe(p.r);
  }
}

int height2_safe(node p)
  requires p::pub_tree<n,_> & p <E @Lo
  ensures res=n & res <E @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + height2_safe(p.l) + height2_safe(p.r);
  }
}

int height3_fail(node p)
  requires p::pri_tree<n,_> & p <E @Hi
  ensures res=n & res <E @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + height3_fail(p.l) + height3_fail(p.r);
  }
}

int height4_safe(node p)
  requires p::pri_tree<n,_> & p <E @Hi
  ensures res=n & res <E @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + height4_safe(p.l) + height4_safe(p.r);
  }
}
