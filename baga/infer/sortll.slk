data node2 {
  int val;
  node2 next;
}.

pred sortll<n,mn> == self::node2<mn,null> & n=1
     or self::node2<mn,q> * q::sortll<n-1,mn1> & mn<=mn1
     .
