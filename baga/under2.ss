/* avl trees */

/* representation of a node in an avl tree */
data node {
  int val;
  int height;
  node left;
  node right;
}

/* view for avl trees */
avl<size, height> == self = null & size = 0 & height = 0
  or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> & size = 1+size1+size2 &
  height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1
  /* inv_exact BG([],self=null & size=0 & height=0) | BG([self],size>0 & height>0) */ // false when use with inv_exact
  inv_sat BG([],self=null & size=0 & height=0) | BG([self],size=1 & height=1)
  /* inv_sat BG([],self=null & size=0 & height=0) | BG([self],size>0 & height>0) */
  ;

 int foo()
requires true
    ensures true;
{
  return 1;
}
