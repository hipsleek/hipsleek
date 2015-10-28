data node {
  int val;
  node next;
}


relation R(node x).

int hoo(node x)
  infer [@ana_ni,R]
  requires R(x)
  ensures true;
{
  int y = x.val;
  return y;
}


/*
# ex2a.ss -p hoo


*/


