data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

  node remove (node x, int d)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  node tmp = null;
  node prev = null;

  tmp = x;
  while (tmp != null)
    infer[H1,G1]
      requires H1(x)
      ensures G1(x,x');//'
    {
      if (tmp.val == d)
        {
          if (prev != null)
            prev.next = tmp.next;
          else
            x = tmp.next;

          break;
        }
      prev = tmp;
      tmp = prev.next;
    }

  return x;
}

/*

*/
