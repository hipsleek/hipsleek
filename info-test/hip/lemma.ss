data node {
  int v;
  node n;
}

data node2 {
  int v;
  node p;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self<?@Lo
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred fpri_ll<n> == self=null & n=0 & self<?@Hi
  or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self<?@Hi
  or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "public->first_private_safe" self::pub_ll<n> -> self::fpri_ll<n>;
lemma_safe "first_private->public_fail" self::fpri_ll<n> -> self::pub_ll<n>;
lemma_safe "public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;
lemma_safe "private->first_private_fail" self::pri_ll<n> -> self::fpri_ll<n>;
lemma_safe "first_private->private_safe" self::fpri_ll<n> -> self::pri_ll<n>;

pred pub_dll<p,n> == self=null & n=0 & self<?@Lo
  or self::node2<v,p,q> * q::pub_dll<q1,m> & n>0 & m=n-1 & self=q1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred pri_dll<p,n> == self=null & n=0 & self<?@Hi
  or self::node2<v,p,q> * q::pri_dll<q1,m> & n>0 & m=n-1 & self=q1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "dll__public->private_safe" self::pub_dll<p,n> -> self::pri_dll<p,n>;
lemma_safe "dll__private->public_fail" self::pri_dll<p,n> -> self::pub_dll<p,n>;
