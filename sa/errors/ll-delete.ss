data node {
  int val;
  node next;
}

HeapPred H(node a, int v).
  HeapPred G(node a, int v, node b).

node delete(node x, int a)
  infer[H,G]
  requires H(x,a)
     ensures G(x,a,res) ;
{
  if (x == null)
    return x;
  else if (x.val == a)
    {
      return x.next;
    }
  else
    {
      x.next = delete(x.next, a);
      return x;
    }
}

/*
H'(x) := x = null \/ x::node(val,next) \/ x::node(val,next) * H'(next)
G'(x,a,res) := res = null \/ x::node(val,next) & res = next & val = a \/ x::node(val,v) * G'(next,a,v) & res = x & val != a


requires H'(x)
ensures G'(x,a,res)
*/
