data node {
        int val;
        node next;
}

data node1 {
        int val;
        node2 next;
}

data node2 {
        int val;
        node1 next;
}

/* mutual-recursive data structures supported */

ll3<n> ==
     self =null & n=0
     or self::node1<_,q> & q=null & n=1
     or self::node1<_,q> * q::node2<_,r> * r::ll3<n-2>
inv n>=0;

/*
Exception occurred: Failure("View definitions are mutually recursive")
Error(s) detected at main 

ll1<n> ==
     self =null & n=0
     or self::node<_,q>*q::ll2<n-1>
  inv n>=0;

ll2<n> ==
     self =null & n=0
     or self::node<_,q>*q::ll1<n-1>
  inv n>=0;
*/

ll_tail<n, t> ==
  self::node< _, null> & t=self & n=0  //empty list
  or self::node<sm, r> * r::ll_tail<n-1, t> & r!=null
  inv n>=0 & self!=null & t!=null;

ll_ht<n, h, t> == self::node<_, r> * r::ll_tail<n, t> & self=h
  inv n>=0 & self!=null & self=h & t!=null;


