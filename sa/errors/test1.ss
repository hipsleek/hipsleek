data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

/* return the last element */
  int get_last(node x)
infer[H,G]  requires H(x)   ensures G(x);//'
/*  requires x::node<v,p>
 case { p = null -> ensures x::node<_, p>;
        p!= null -> ensures x::node<_, p>;
        }*/
{
  if (x.next !=null)
    { x.val =1;}
  else {x.val=0;}
  return x.val;
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
