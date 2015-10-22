data node {
  int val;
  node next;
}


//relation R(node x).

int hoo(node x)
  infer [@ana_ni,@shape_pre]//,R]
  requires true // R(x)
  ensures true;
{
  int y = x.val;
  return y;
}


/*
# ex2a.ss -p hoo

******pure relation assumption 1 *******
*************************************
[RELASS [R]: ( R(x)) -->  2<=x]
*************************************

*/


