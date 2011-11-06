data node {
  int val;
}

void main()
  requires true
  ensures true;
{
  node p = new node(1);
  node q = p;
  q.val = 2;
  assert p.val!=2;
  return;
}


void main2(node p, node q)
  requires p::node<1> & p=q
  ensures p::node<2> & p=q;
{
  q.val = 2;
  assert p.val!=2;
  return;
}
