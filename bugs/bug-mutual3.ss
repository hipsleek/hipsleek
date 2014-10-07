data node {
        int val;
        node next;
}

/* mutual-recursive data structures supported */

ll1<n> ==
     self =null & n=0
     or self::node<_,q>*q::ll2<n-1>
  inv n>=0;

ll2<n> ==
     self =null & n=0
     or self::node<_,q>*q::ll1<n-1>
  inv n>=0;

