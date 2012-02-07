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
	inv size >= 0 & height >= 0;



/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)

	requires x::avl<m, n>
	ensures res::avl<m+1, _>;



node merge(node t1, node t2)
/*

case {
      t1=null -> requires t2::avl<s2,h2> ensures res::avl<s2,h2>;
      t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> & Loop
                  ensures false; 
      //res::avl<s1+s2,_>;
}

 */

case {
      t1=null -> requires t2::avl<s2,h2> ensures res::avl<s2,h2>;
      t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> & Loop
                  ensures false; 
      //res::avl<s1+s2,_>;
}
// incorrect code that LOOPS!

{
 if (t1 == null) return t2;
 else {
	  node tmp = insert(t2, t1.val);
	  node tmp1 = merge (tmp, t1.left);
	  return merge(tmp1, t1.right);
	  }
}

