data node2 {
  node2 left;
  node2 right;
}

data node3 {
  int color;
  node3 left;
  node3 right;
}

btree<n> == self=null & n=0
  or exists l,r,n1,n2: self::node2<l,r> * l::btree<n1> * r::btree<n2> & n=n1+n2+1
  ;

btree2<n,h> == self=null & n=0 & h=0
  or exists l,r,n1,n2,h1,h2: self::node2<l,r> * l::btree2<n1,h1> * r::btree2<n2,h2> & n=n1+n2+1 & h=h2+1
  ;

rbtree<n,cl,bh> == self=null & n=0 & cl=0 & bh=1
  or exists l,r,n1,n2,bh1,bh2: self::node3<1,l,r> * l::rbtree<n1,0,bh1> * r::rbtree<n2,0,bh2> & n=n1+n2+1 & bh=bh1 & bh=bh2
  or exists l,r,n1,n2,bh1,bh2: self::node3<0,l,r> * l::rbtree<n1,_,bh1> * r::rbtree<n2,_,bh2> & n=n1+n2+1 & bh1=bh2 & bh=bh1+1
  ;
