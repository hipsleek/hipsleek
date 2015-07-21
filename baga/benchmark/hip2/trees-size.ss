/* trees & binary search trees */

/* representation of a node */
data node {
	int val; 
	node next;	
}

data node2 {
	int val;
	node2 left;
	node2 right; 
}

/* view for trees with number of nodes */
tree1<m> == self = null & m = 0 
	or self::node2<_, p, q> * p::tree1<m1> * q::tree1<m2> & m = 1 + m1 + m2 
	inv m >= 0; 

/* view for trees with number of nodes and depth */
tree<m, n> == self = null & m = 0 & n = 0 
	or self::node2<_, p, q> * p::tree<m1, n1> * q::tree<m2, n2> & m = 1 + m1 + m2 & n = 1 + max(n1, n2)
	inv m >= 0 & n >= 0;

/* view for a doubly linked list with size */
dll<p, n> == self = null & n = 0 
	or self::node2<_, p, q> * q::dll<self, n1> & n = n1+1
	inv n >= 0;

/* function to append 2 doubly linked lists */
node2 append(node2 x, node2 y)
     requires x::dll<_, m> * y::dll<_, n>
     ensures res::dll<r, m+n>;
{
  node2 z;

  if (x == null)
    return y;
  else{
    z = append(x.right, y);
    x.right = z;
    if (z != null)
      z.left = x;
    return x;
  }
}


/* function to count the number of nodes in a tree */
int count(node2 z)
  requires z::tree1<m>
  ensures z::tree1<m> & res = m & res >= 0;
{
  int cleft, cright;

  if (z == null)
    return 0;
  else{
    cleft = count(z.left);
    cright = count(z.right);
    return (1 + cleft + cright);
  }
}

/* function to transform a tree in a doubly linked list */
void flatten(node2 x)
  requires x::tree<m, n> 
  ensures (exists q : x::dll<q, m> & q=null);
{
  node2 tmp;
  if (x != null){
    flatten(x.left);
    flatten(x.right);
    tmp = append(x.left, x.right);
    x.left = null;
    x.right = tmp;
    if (tmp != null)
      tmp.left = x;
  }
}
