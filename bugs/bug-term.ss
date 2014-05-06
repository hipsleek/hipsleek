data node2 {
  int val;
  node2 left;
  node2 right;
}

data node {
  int val;
  node next;
}

// linked-list of nodes
ll<n> == self=null & n=0
  or self::node<v,q>*q::ll<n-1> 
  inv n>=0;

// binary tree where m is number of leaves
tree2<m> == self=null & m=1
  or self::node2<v,p,q> * p::tree2<m1> * q::tree2<m2> & m=m1+m2
  inv m>=1;


// append method to join two lists together
node append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & Term[n1]
  ensures res::ll<n1+n2> ;

/* 
   Write the strongest postcondition for the
   specification below.

   Add the smallest termination condition for the
   method below.
*/
// flattens a tree of nodes into a list of nodes
node flatten(node2 t)
  requires t::tree2<m> & Term[m]
  ensures res::ll<n>;
{
  if (t==null) {
    return null;
  } else {
    node l1 = flatten(t.left);
    node l2 = flatten(t.right);
    node l3 = new node(t.val,l1);
    return append(l2,l3);
  }
}

