data node {
  int val;
  node left;
  node right;
}

node get_max(node x)
{
  if (x == null)
    return null;
  else if (x.right == null)
    return x;
  else
    return get_max(x.right);
}
