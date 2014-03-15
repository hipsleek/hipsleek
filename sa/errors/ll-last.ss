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
G(x,res) ::= 
 x::node<val,next>@M * G(next,res)&next!=null
 or x::node<val,next>@M&res=x & next=null


G(x,res) ::= lseg(x,p) * p::node<_,_>

 x::node<val,next>@M * G(next,res)&next!=null
 or x::node<val,next>@M&res=x & next=null

 */
/*
loop 1:
p1 x=null
p2 x!=null & x.next=null
p3 x!=null & x.next!=null

loop2:

loop3:

 */

/*
H'(x) := x::node(val,next) & next = null \/ x::node(val,next) * H'(next) & next != null
G'(x,res) := x::node(val,next) & next = null & res = x \/ x::node(val,next) * G'(next,res) & next != null

case x == null =>
  ensures res = null;
case x != null =>
  requires H'(x)
  ensures G'(x,res);
*/
