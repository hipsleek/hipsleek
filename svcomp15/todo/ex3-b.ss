data node{int v;}

data node2{int v;
  node next;
}

/*
void free(node2 x)
  requires x::node2<_,_>
  ensures emp & true;

void free(node x)
  requires x::node<_>
  ensures emp & true;
*/

void test(node x)
  requires x::node<_>
  ensures emp & true;
{
  free(x);
  return;
}
