data node {
  int v;
  node n;
}

pred pub_ll<n> == self=null & n=0 & self <E @Lo
               or self::node<v,q> * q::pub_ll<m> & n>0 & m=n-1 & self <E @Lo & v <E @Lo
              inv n>=0;
pred pri_ll<n> == self=null & n=0 & self <E @Hi
               or self::node<v,q> * q::pri_ll<m> & n>0 & m=n-1 & self <E @Hi & v <E @Hi
              inv n>=0;

lemma_safe "safe->unsafe" self::pub_ll<n> -> self::pri_ll<n>;
lemma_safe "unsafe->safe_fail" self::pri_ll<n> -> self::pub_ll<n>;
