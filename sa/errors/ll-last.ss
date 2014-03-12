data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

/* return the last element */
  node get_last(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);//'
{
  if (x == null) return null;
  /* else { */
  /*   while (x.next != null) */
  /*     infer[H1,G1] */
  /*       requires H1(x) */
  /*       ensures G1(x,x');//' */
  /*     { */
  /*       x = x.next; */
  /*     } */
  /*   return x; */
  /* } */
  else if (x.next == null) return x;
  else return get_last(x.next);
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
