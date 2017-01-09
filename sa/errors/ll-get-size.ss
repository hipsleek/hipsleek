data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, int b).

/* return the tail of a singly linked list */
  int get_size(node x)
  infer[H,G]
  requires H(x)
     ensures G(x,res);
{
  if(x == null) 
    return 0;
  else {
    return get_size(x.next) + 1;
  }
}

/*
H'(x) := x = null \/ x::node(val,next) * H'(next)
G'(x,res) := x = null & res = 0 \/ x::node(val,next) * G(next,v) & res = v + 1

requires H'(x)
ensures G'(x,res);
*/
