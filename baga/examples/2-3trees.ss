/* 2-3 trees */
data node3 {
  int maxl;	// max left
  int maxm;	// max middle
  node3 left;
  node3 middle;
  node3 right;
}

// TODO: to check the intermediate value... sometimes I just put 0, 0

tree2_3<n> == self = null & n = 0
  or self::node3<_, _, l, m, r> * l::tree2_3<ln> * m::tree2_3<mn> * r::tree2_3<rn>
  & r != null & ln = mn & ln = rn & n = ln + 1
  or self::node3<_, _, l, m, r> * l::tree2_3<ln> * m::tree2_3<mn>
  & r = null & ln = mn & n = ln + 1
  inv n >= 0
  /* inv_exact BG([],self=null & n=0) | BG([self],n>0) */
  /* inv_sat BG([],self=null & n=0) | BG([self],n>0) */
  ;

/*tree2_3<n> == self = null & n = 0
  or self::node3<_, _, l, m, r> * l::tree2_3<ln> * m::tree2_3<mn> * r::tree2_3<rn>
  & r = null & l = null & m = null & n = 1

  or self::node3<_, _, l, m, r> * l::tree2_3<ln> * m::tree2_3<mn> * r::tree2_3<rn>
  & r != null & l != null & m != null & ln = mn & mn = rn & n = ln + 1

  or self::node3<_, _, l, m, r> * l::tree2_3<ln> * m::tree2_3<mn> * r::tree2_3<rn>
  & r = null & l != null & m != null & ln = mn & n = ln + 1

  inv n >= 0;*/

void  make_node(node3 tmp1, int a)
  requires tmp1::node3<_, _, l, m, r> * l::tree2_3<n> * m::tree2_3<n> & r = null & n = 1
  ensures tmp1::tree2_3<2> ;
{
  if (a < tmp1.maxl) {
    tmp1.right = tmp1.middle;
    tmp1.middle = tmp1.left;
    tmp1.left = new node3(a, 0, null, null, null);
  }
  else {
    if (a < tmp1.maxm) {
      tmp1.right = tmp1.middle;
      tmp1.middle = new node3(a, 0, null, null, null);
    }
    else
      tmp1.right = new node3(a, 0, null, null, null);
  }
  return;
}

node3 insert_left(node3@R x, int a, int type)
  requires x::tree2_3<n> & n > 1
  ensures res::tree2_3<n+1> & x' = null & n>1 or
	  x'::tree2_3<n> & x = x' & res = null & n>1;
  requires x::node3<_, _, l, m, r> * l::tree2_3<n1> * m::tree2_3<n1> & n1 > 0 & r = null
  ensures x'::tree2_3<n1+1> & x = x' & res = null & n1>0;  //'
{
  node3 tmp1, tmp2;
  if (type == 1)
    tmp1 = x.left;
  else
    tmp1 = x.middle;
  if(tmp1.left != null && tmp1.right == null) {
    insert(tmp1, a);
    //dprint;
    return null;
  }
  else {
    if (a < tmp1.maxl) {				// insert in the left subtree
      tmp2 = insert(tmp1.left, a);
      if(tmp2 != null) {
        tmp1.left = tmp1.middle;
        tmp1.middle = tmp1.right;
        tmp1.right = null;
      }
      else {
        if (a < tmp1.maxm) {		// insert in the middle subtree
          tmp2 = insert(tmp1.middle, a);
          if(tmp2 != null) {
            tmp1.middle = tmp1.right;
            tmp1.right = null;
          }
        }
        else {				// insert in the right subtree
          tmp2 = insert(tmp1.right, a);
          if (tmp2 != null) {
            tmp1.right = null;
          }
        }
      }
    }
    if (tmp2 != null) {
      if(type == 1) {
        if(x.right == null) {			// x has 2 children
          x.right = x.middle;
          x.middle = x.left;
          x.left = tmp2;
          return null;
        }
        else {					// x has 3 children
          node3 newnode;
          newnode = new node3(0, 0, tmp2, x.left, null);
          x.left = x.middle;
          x.middle = x.right;
          x.right = null;
          node3 aux = new node3(0, 0, newnode, x, null);
          x = null;
          return aux;
        }
      }
      else {
        if(x.right == null) {			// x has 2 children
          x.right = x.middle;
          x.middle = tmp2;
          return null;
        }
        else {					// x has 3 children
          node3 newnode = new node3(0, 0, x.left, tmp2, null);
          x.left = x.middle;
          x.middle = x.right;
          x.right = null;
          node3 aux = new node3(0, 0, newnode, x, null);
          x = null;
          return aux;
        }
      }
    }
    else return null;
  }
}

node3 insert_middle(node3@R x, int a)
  requires x::tree2_3<n> & n > 1
  ensures res::tree2_3<n+1> & x' = null & n>1 or
	x'::tree2_3<n> & x = x' & res = null & n>1;
  requires x::node3<_, _, l, m, r> * l::tree2_3<n1> * m::tree2_3<n1> & n1 > 0 & r = null
  ensures x'::tree2_3<n1+1> & x = x' & res = null & n1>0; //'
{
  node3 tmp1, tmp2;
  tmp1 = x.middle;
  if(tmp1.left != null && tmp1.right == null) {
    insert(tmp1, a);
    return null;
  }
  else {
    if (a < tmp1.maxl) {				// insert in the left subtree
      tmp2 = insert(tmp1.left, a);
      if(tmp2 != null) {
        tmp1.left = tmp1.middle;
        tmp1.middle = tmp1.right;
        tmp1.right = null;
      }
      else {
        if (a < tmp1.maxm) {		// insert in the middle subtree
          tmp2 = insert(tmp1.middle, a);
          if(tmp2 != null) {
            tmp1.middle = tmp1.right;
            tmp1.right = null;
          }
        }
        else {				// insert in the right subtree
          tmp2 = insert(tmp1.right, a);
          if (tmp2 != null) {
            tmp1.right = null;
          }
        }
      }
    }
    if (tmp2 != null) {
      if(x.right == null) {			// x has 2 children
        x.right = x.middle;
        x.middle = tmp2;
        return null;
      }
      else {					// x has 3 children
        node3 newnode = new node3(0, 0, x.left, tmp2, null);
        x.left = x.middle;
        x.middle = x.right;
        x.right = null;
        node3 aux = new node3(0, 0, newnode, x, null);
        x = null;
        return aux;
      }
    }
    else return null;
  }
}

node3 insert_right(node3@R x, int a)
  requires x::node3<_, _, l, m, r> * l::tree2_3<n1> * m::tree2_3<n1> * r::tree2_3<n1>  & n1 > 0
  ensures res::tree2_3<n1+2> & x' = null & n1>0 or
	x'::tree2_3<n1+1> & x = x' & res = null & n1>0; //'
{
  node3 tmp1, tmp2;
  tmp1 = x.right;
  if(tmp1.left != null && tmp1.right == null) {
    insert(tmp1, a);
    return null;
  }
  else {
    if (a < tmp1.maxl) {				// insert in the left subtree
      tmp2 = insert(tmp1.left, a);
      if(tmp2 != null) {
        tmp1.left = tmp1.middle;
        tmp1.middle = tmp1.right;
        tmp1.right = null;
      }
      else {
        if (a < tmp1.maxm) {		// insert in the middle subtree
          tmp2 = insert(tmp1.middle, a);
          if(tmp2 != null) {
            tmp1.middle = tmp1.right;
            tmp1.right = null;
          }
        }
        else {				// insert in the right subtree
          tmp2 = insert(tmp1.right, a);
          if (tmp2 != null) {
            tmp1.right = null;
          }
        }
      }
    }
    if (tmp2 != null) {
      // x has 3 children
      node3 newnode = new node3(0, 0, x.right, tmp2, null);
      x.right = null;
      node3 aux = new node3(0, 0, x, newnode, null);
      x = null;
      return aux;
    }
    else return null;
  }
}

node3 insert(node3@R x, int a)
  requires x::tree2_3<n>
  ensures res::tree2_3<n+1> & x' = null or
	  x'::tree2_3<n> & x = x' & res = null & x' != null ;
  requires x::node3<_, _, l, m, r> * l::tree2_3<n> * m::tree2_3<n> & n>0 & r = null
  ensures  x'::tree2_3<n+1> & x = x' & res = null & n>0;
{
  node3 leaf = new node3(a, 0, null, null, null);		// creating a new leaf node
  if (x == null) {					// x is empty
    return leaf;
  }
  else {
    if (x.left == null) {				// x is a leaf
      if (x.maxl <= a) {
        node3 aux = new node3(x.maxl, a, x, leaf, null);
        x = null;
        return aux;
      }
      else {
        node3 aux = new node3(a, x.maxl, leaf, x, null);
        x = null;
        return aux;
      }
    }
    else {						// x is an internal node
      node3 tmp1, tmp2;
      if(a < x.maxl) {			// we have to insert in the left substree
        return insert_left(x, a, 1);
      }
      else {
        if(a < x.maxm) return insert_middle(x, a);
        else {
          if(x.right == null) return insert_middle(x, a);
          else return insert_right(x, a);
        }
      }
    }
  }
}
