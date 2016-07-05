data node {
 int val;
 node next@REC;
}

data node2 {
 int val;
 node2 left;
 node2 right;
}

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;

/*
  ll<n:int> == self=null & n=0
  or self::node<v,q>*q::ll<n-1>& self!=null
 inv true;
*/

lseg<p> == self=p
  or self::node<v,q>*q::lseg<p>& self!=null
 inv true;

lseg1<p,n> == extends lseg<p> with size[REC]<n> .

  /*
lseg<p,n:int> == self=p & n=0
  or self::node<v,q>*q::lseg<p,n-1>& self!=null
 inv n>=0;

bst<n:int> == self=null & n=0
  or self::node2<v,l,r>*l::bst<n1> * r::bst<n2> & n=n1+n2+1 & self!=null
 inv n>=0;
  */
