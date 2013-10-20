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
	/* requires a >= 0  */
	/* ensures res::ll<>; */
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
