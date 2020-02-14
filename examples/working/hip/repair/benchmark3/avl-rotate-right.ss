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
	or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> &
  size = 1+size1+size2 & height2<=height1+1 & height1<=height2+1 &
  height = max(height1, height2) + 1
	inv size >= 0 & height >= 0;

/* function to return the height of an avl tree */
int height(node x)

	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;        
}

node node_error() requires true ensures false;

/* function to insert a node in an avl tree (using the rotate functions) */
node rotate_right(node x)
	requires x::node<_, lrht+3, xleft, xright> * xright::avl<rsize, lrht> *
           xleft::node<_,lrht+2, xleftleft, xleftright>
           * xleftleft::avl<llsize, lrht + 1> * xleftright::avl<lrsize, lrht>
	ensures res::avl<rsize + llsize + lrsize + 2, lrht + 2>;

	requires x::node<_, lrht+3, xleft, xright> * xright::avl<rsize, lrht> *
           xleft::node<_,lrht+2, xleftleft, xleftright>
           * xleftleft::avl<llsize, lrht + 1> * xleftright::avl<lrsize, lrht>
	ensures res::avl<rsize + llsize + lrsize + 2, lrht + 2>;


{
   node left = x.left;

   if (height(left) == height(x.right) + 2){
      int llht = height(left.left);
      int lrht = height(left.right);

      if (llht > lrht){
          x.height = lrht + 1;
          x.left = left.right;
          // Correct: left.height = lrht + 2;
          left.height = lrht + 2;
          left.right = x;
          return left;
      }
      else return node_error();
   }
   else return node_error();
}

