data node {
  int val;
  int height;
  node left;
  node right;
}

/* view for avl trees */
avl<n, h> == 
  self = null & n = 0 & h = 0 or 
  self::node<_, h, p, q> * p::avl<n1, h1> * q::avl<n2, h2>
    & n = 1+n1+n2
    & h2<=h1+1 & h1<=h2+1 & h = max(h1, h2) + 1 
  inv n >= 0 & h >= 0;

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
  requires x::avl<m, n> & Term[m]
  ensures res::avl<m + 1, n1> & n <= n1 <= n+1;

node merge(node t1, node t2)
  infer [@term]
  requires t1::avl<s1, h1> * t2::avl<s2, h2>
  ensures res::avl<s1+s2, _>;
  
  /*
  case {
    t1=null -> requires t2::avl<s2, h2> & Term ensures res::avl<s2, h2>;
    t1!=null -> requires t1::avl<s1, h1> * t2::avl<s2, h2> & Term[s1] ensures res::avl<s1+s2, _>;
  }
  */
{
  if (t1 == null) return t2;
  else {
    node tmp = insert(t2, t1.val);
    node tmp1 = merge (t1.left, tmp);
    return merge(t1.right, tmp1);
  }
}

node merge2(node t1, node t2)
  infer [@term]
  requires t1::avl<s1, h1> * t2::avl<s2, h2>
  ensures res::avl<s1+s2, _>;
  
  /*
  case {
    t1=null -> requires t2::avl<s2,h2> & Term ensures res::avl<s2,h2>;
    t1!=null -> requires t1::avl<s1,h1> * t2::avl<s2,h2> & Loop ensures false;
  }
  */
{
  if (t1 == null) return t2;
  else {
    node tmp = insert(t2, t1.val);
    node tmp1 = merge2(tmp, t1.left);
    return merge2(tmp1, t1.right);
  }
}

