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
  return 0;
}


/*
# ex2a.ss -p hoo


*/


