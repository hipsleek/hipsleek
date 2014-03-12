data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

/* return the last element */
  node get_last(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  if (x == null) return null;
  else {
    while (x.next != null) {
      x = x.next;
    }
    return x;/* if (x.next == null) return x; */
    /* else return get_last(x.next); */
  }
}

/*
H'(x) := x::node(val,next) & next = null \/ x::node(val,next) * H'(next) & next != null
G'(x,res) := x::node(val,next) & next = null & res = x \/ x::node(val,next) * G'(next,res) & next != null

case x == null =>
  ensures res = null;
case x != null =>
  requires H'(x)
  ensures G'(x,res);
*/
