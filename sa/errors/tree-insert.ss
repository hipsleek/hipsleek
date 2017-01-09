data node {
  int val;
  node left;
  node right;
}

node insert(node x, int a)
{
  if (x == null) {
    return new node(a, null, null);
  } else if (x.val == a) {
    return x;
  } else if (x.val > a) {
    if (x.left == null) {
      x.left = new node(a, null, null);
    } else {
      x.left = insert(x.left, a);
    }
    return x;
  } else {
    if (x.right == null) {
      x.right = new node(a, null, null);
    } else {
      x.right = insert(x.right, a);
    }
    return x;
  }
}
