data node {
  int val;
  node next;
}

HeapPred H(node a, int b).
  HeapPred G(node a, int b, node c).

  node insert(node x, int a)
  infer[H,G]
  requires H(x,a)
     ensures G(x,a,res);
{
  if (x == null)
    return new node(a, null);
  else if (x.next == null)
    {
      x.next = new node(a, null);
      return x;
    }
  else
    {
      x.next = insert(x.next, a);
      return x;
    }
}

/*
H'(x) := x::node(val,next) & next = null \/ x::node(val,next) * H'(next) & next != null
G'(x,a,res) := x::node(val,next) * next::node(a,null) & res = x \/ x::node(val,v) * G'(next,a,v) & res = x & next != null

case x == null =>
  ensures res::node(a,null);
case x != null =>
  requires H'(x)
  ensures G'(x,a,res);
*/
