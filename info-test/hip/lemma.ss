data ll_node {
  int v;
  ll_node n;
}

data dll_node {
  int v;
  dll_node p;
  dll_node n;
}

data tree_node {
  int v;
  tree_node l;
  tree_node r;
}

pred pub_ll<n> == self=null & n=0 & self<?@Lo
  or self::ll_node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred fpri_ll<n> == self=null & n=0 & self<?@Hi
  or self::ll_node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;
pred pri_ll<n> == self=null & n=0 & self<?@Hi
  or self::ll_node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "ll__public->first_private_safe" self::pub_ll<n> -> self::fpri_ll<n>;
lemma_safe "ll__first_private->public_fail" self::fpri_ll<n> -> self::pub_ll<n>;
lemma_safe "ll__public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "ll__private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;
lemma_safe "ll__private->first_private_fail" self::pri_ll<n> -> self::fpri_ll<n>;
lemma_safe "ll__first_private->private_safe" self::fpri_ll<n> -> self::pri_ll<n>;

pred pub_dll<p,n> == self=null & n=0 & self<?@Lo
  or self::dll_node<v,p,q> * q::pub_dll<q1,m> & n>0 & m=n-1 & self=q1 & self<?@Lo & v<?@Lo
  inv n>=0;
pred pri_dll<p,n> == self=null & n=0 & self<?@Hi
  or self::dll_node<v,p,q> * q::pri_dll<q1,m> & n>0 & m=n-1 & self=q1 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "dll__public->private_safe" self::pub_dll<p,n> -> self::pri_dll<p,n>;
lemma_safe "dll__private->public_fail" self::pri_dll<p,n> -> self::pub_dll<p,n>;

pred pub_tree<n> == self=null & n=0 & self<?@Lo
  or self::tree_node<v,l,r> * l::pub_tree<n1> * r::pub_tree<n2>
     & n=n1+n2 & n>0 & self<?@Lo & v<?@Lo
  inv n>=0;

pred pri_tree<n> == self=null & n=0 & self<?@Hi
  or self::tree_node<v,l,r> * l::pri_tree<n1> * r::pri_tree<n2>
     & n=n1+n2 & n>0 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "tree__public->private_safe" self::pub_tree<n> -> self::pri_tree<n>;
lemma_safe "tree__private->public_fail" self::pri_tree<n> -> self::pub_tree<n>;
