//from xisa

data dllist {
  int val;
  dllist prev;
  dllist next;
}

dllist malloc()
  requires true
  ensures res::dllist<_,_,_> or res=null;

HeapPred H1(dllist a).
HeapPred G1(dllist a).
dllist create()
	/* requires a >= 0  */
	/* ensures res::ll<>; */
  infer[G1]
  requires true
  ensures G1(res);
{
  dllist tmp;
  dllist n;

  tmp = create();
  n = malloc ();
  if (n!=null) {
    n.next = tmp;
    n.prev = null;
    n.val = 0;
    return n;
  }
  return null;
}


dllist copy(dllist l)
  infer[H1,G1]
  requires H1(l)
  ensures G1(res);
{
  dllist tmp;
  dllist n;

  if (l!=null) {
    tmp = copy(l.next);
    n = malloc ();
    if (n!=null) {
      n.next = tmp;
      n.prev = l.prev;
      n.val = l.val;
      return n;
    }
    return null;
  }
  else return null;
}

void findnbackloop(dllist l, int x) {
  //ListNode* nil = NULL;  // To make graphs easier to follow.
  dllist prev;
  dllist curr;

  //_spec_assume("add_edge(kind_C[(l) =dllist((nil))=>])");

  curr = l;
  while (curr != null) {
    if (curr->data == x) { break; }
    curr = curr->next;
  }

  if (curr != NULL) {
    prev = curr->prev;

    while (prev != NULL) {
      curr = prev;         // To name the middle node.
      prev = prev->prev;
    }
  }
}


