data node {
  int val;
  node next;
}

HeapPred H(node a, node b).
  HeapPred G(node a, node b, node c).

node append(node x, node y)
  infer[H,G]
  requires H(x,y)
     ensures G(x,y,res);

{
  if (x == null)
    return y;
  else if (x.next == null)
    {
      x.next = y;
      return x;
    }
  else
    {
      x.next = append(x.next, y);
      return x;
    }
}

/*
H'(x) := x::node(val,next) & next = null \/ x::node(val,next) * H'(next) & next != null
G'(x,y,res) := x::node(val,y) & res = x \/ x::node(val,v) * G'(next,y,v) & res = x & next != null

case x == null =>
  ensures res = y;
case x != null =>
  requires H'(x)
  ensures G'(x,y,res);
*/
