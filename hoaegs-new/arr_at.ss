data node {
  int val;
  node next;
}

//relation dom(int[] a, int x, int y) == true.
//relation dom(int[] b, int x, int y) == true.

int main(node n)
  requires n::node<a,b>
  ensures res=1;
{
  dprint;
  n.val = 1;
  dprint;
  return n.val;
  dprint;
}
