data node {
  int v;
  node n;
  node p;
}

pred pub_dll<n,p> == self=null & n=0 & self<?@Lo
  or self::node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred pri_dll<n,p> == self=null & n=0 & self<?@Hi
  or self::node<v,q,p> * q::pri_dll<m,self> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "public->private_safe" self::pub_dll<n,p> -> self::pri_dll<n,p>;
lemma_safe "private->public_fail" self::pri_dll<n,p> -> self::pub_dll<n,p>;

int length1_safe(node p)
  requires p::pub_dll<n,_> & p <? @Lo
  ensures res=n & res <? @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + length1_safe(p.n);
  }
  dprint;
}

int length2_safe(node p)
  requires p::pub_dll<n,_> & p <? @Lo
  ensures res=n & res <? @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + length2_safe(p.n);
  }
}

int length3_fail(node p)
  requires p::pri_dll<n,_> & p <? @Hi
  ensures res=n & res <? @Lo;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + length3_fail(p.n);
  }
}

int length4_safe(node p)
  requires p::pri_dll<n,_> & p <? @Hi
  ensures res=n & res <? @Hi;
{
  if(p == null) {
    return 0;
  } else {
    return 1 + length4_safe(p.n);
  }
}
