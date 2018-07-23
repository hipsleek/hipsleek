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

data tree_node_par {
  int v;
  tree_node_par l;
  tree_node_par r;
  tree_node_par p;
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

pred ff_pri_ll<n,m> == self::pub_ll<m> & n=0 & self<?@Lo
  or self::ll_node<v,q> * q::ff_pri_ll<n-1,m> & n>0 & self<?@Hi & v<?@Hi
  inv n>=0 & m>=0;

lemma_safe "ll__public->first_private_safe" self::pub_ll<n> -> self::fpri_ll<n>;
lemma_safe "ll__first_private->public_fail" self::fpri_ll<n> -> self::pub_ll<n>;
lemma_safe "ll__public->private_safe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "ll__private->public_fail" self::pri_ll<n> -> self::pub_ll<n>;
lemma_safe "ll__private->first_private_fail" self::pri_ll<n> -> self::fpri_ll<n>;
lemma_safe "ll__first_private->private_safe" self::fpri_ll<n> -> self::pri_ll<n>;

pred pub_dll<n,p> == self=null & n=0 & self <? @Lo
  or self::dll_node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self <? @Lo & v <? @Lo
  inv n>=0;
pred fpri_dll<n,p> == self=null & n=0 & self <? @Hi
  or self::dll_node<v,q,p> * q::pub_dll<m,self> & n>0 & m=n-1 & self <? @Hi & v <? @Hi
  inv n>=0;
pred pri_dll<n,p> == self=null & n=0 & self <? @Hi
  or self::dll_node<v,q,p> * q::pri_dll<m,self> & n>0 & m=n-1 & self <? @Hi & v <? @Hi
  inv n>=0;

lemma_safe "dll__public->dll__first_private_safe" self::pub_dll<n,p> -> self::fpri_dll<n,p>;
lemma_safe "dll__first_private->dll__public_fail" self::fpri_dll<n,p> -> self::pub_dll<n,p>;
lemma_safe "dll__public->dll__private_safe" self::pub_dll<n,p> -> self::pri_dll<n,p>;
lemma_safe "dll__private->dll__public_fail" self::pri_dll<n,p> -> self::pub_dll<n,p>;
lemma_safe "dll__private->dll__first_private_fail" self::pri_dll<n,p> -> self::fpri_dll<n,p>;
lemma_safe "dll__first_private->dll__private_safe" self::fpri_dll<n,p> -> self::pri_dll<n,p>;

pred pub_tree<n> == self=null & n=0 & self<?@Lo
  or self::tree_node<v,l,r> * l::pub_tree<n1> * r::pub_tree<n2>
     & n=n1+n2+1 & n>0 & self<?@Lo & v<?@Lo
  inv n>=0;

pred pri_tree<n> == self=null & n=0 & self<?@Hi
  or self::tree_node<v,l,r> * l::pri_tree<n1> * r::pri_tree<n2>
     & n=n1+n2+1 & n>0 & self<?@Hi & v<?@Hi
  inv n>=0;

lemma_safe "tree__public->private_safe" self::pub_tree<n> -> self::pri_tree<n>;
lemma_safe "tree__private->public_fail" self::pri_tree<n> -> self::pub_tree<n>;

pred pub_tree_par<n,p> == self=null & n=0 & self <? @Lo
  or self::tree_node_par<v,l,r,p> * l::pub_tree_par<ln,self> * r::pub_tree_par<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Lo & v <? @Lo
  inv n>=0;
pred pri_tree_par<n,p> == self=null & n=0 & self <? @Hi
  or self::tree_node_par<v,l,r,p> * l::pri_tree_par<ln,self> * r::pri_tree_par<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Hi & v <? @Hi
  inv n>=0;

lemma_safe "tree__public_par->tree__private_par_safe" self::pub_tree_par<n,p> -> self::pri_tree_par<n,p>;
lemma_safe "tree__private_par->tree__public_par_fail" self::pri_tree_par<n,p> -> self::pub_tree_par<n,p>;

pred lpub_tree<n> == self=null & n=0 & self<?@Lo
  or self::tree_node<v,l,r> * l::pub_tree<n1> * r::pri_tree<n2>
  & n=n1+n2+1 & n>0 & self<?@Lo & v<?@Lo
  inv n>=0;

pred rpub_tree<n> == self=null & n=0 & self<?@Lo
  or self::tree_node<v,l,r> * l::pri_tree<n1> * r::pub_tree<n2>
  & n=n1+n2+1 & n>0 & self<?@Lo & v<?@Lo
  inv n>=0;

lemma_safe "tree__l_public->tree__public_fail" self::lpub_tree<n> -> self::pub_tree<n>;
lemma_safe "tree__r_public->tree__public_fail" self::rpub_tree<n> -> self::pub_tree<n>;
lemma_safe "tree__l_public->tree__private_safe" self::lpub_tree<n> -> self::pri_tree<n>;
lemma_safe "tree__r_public->tree__private_safe" self::rpub_tree<n> -> self::pri_tree<n>;
lemma_safe "tree__tree__private->l_public_fail" self::pri_tree<n> -> self::lpub_tree<n>;
lemma_safe "tree__tree__private->r_public_fail" self::pri_tree<n> -> self::rpub_tree<n>;

pred lpub_tree_par<n,p> == self=null & n=0 & self <? @Lo
  or self::tree_node_par<v,l,r,p> * l::pub_tree_par<ln,self> * r::pri_tree_par<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Lo & v <? @Lo
  inv n>=0;

pred rpub_tree_par<n,p> == self=null & n=0 & self <? @Lo
  or self::tree_node_par<v,l,r,p> * l::pri_tree_par<ln,self> * r::pub_tree_par<rn,self>
  & n>0 & n=ln+rn+1 & self <? @Lo & v <? @Lo
  inv n>=0;

lemma_safe "tree__l_public_par->tree__public_par_fail" self::lpub_tree_par<n,p> -> self::pub_tree_par<n,p>;
lemma_safe "tree__r_public_par->tree__public_par_fail" self::rpub_tree_par<n,p> -> self::pub_tree_par<n,p>;
lemma_safe "tree__l_public_par->tree__private_par_safe" self::lpub_tree_par<n,p> -> self::pri_tree_par<n,p>;
lemma_safe "tree__r_public_par->tree__private_par_safe" self::rpub_tree_par<n,p> -> self::pri_tree_par<n,p>;
lemma_safe "tree__tree__private_par->l_public_par_fail" self::pri_tree_par<n,p> -> self::lpub_tree_par<n,p>;
lemma_safe "tree__tree__private_par->r_public_par_fail" self::pri_tree_par<n,p> -> self::rpub_tree_par<n,p>;
