data node {
  node next;
}

ll1<> == self::node<q> * q::ll1<>
  inv true;

ll<> == self = null
	or self::node<q> * q::ll<>
  inv true;

HeapPred H1(node a).
HeapPred G1(node b, node c).

node malloc(int s)
  requires true
  ensures res::node<_> or res=null;

int for_aux(ref node ptr)
/*
   requires ptr::ll<>
   ensures ptr'::ll<>;//'
*/
   //ensures false;

  infer[H1,G1]
  requires H1(ptr)
  ensures G1(ptr',ptr); //'
{
  node old_ptr = ptr;
  // ptr = new node(old_ptr);
  ptr = malloc(1);
  if (ptr==null) {
    ptr = old_ptr;
    return -1;
  }

  ptr.next = old_ptr;
  for_aux(ptr);
  return 0;
}

