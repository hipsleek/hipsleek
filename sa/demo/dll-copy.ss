//xisa
data dllist {
  int val;
  dllist prev;
  dllist next;
}

dllist malloc()
  requires true
  ensures res::dllist<_,_,_>;

HeapPred H1(dllist a, dllist b, dllist c).
HeapPred G1(dllist a).

void copy_while(ref dllist cur, ref dllist n, ref dllist newprev)
  infer[H1,G1]
  requires H1(cur, n, newprev)
  ensures G1(n');//'
{
 
  if (cur !=null){
  n = malloc();
  n.next = null;
  n.prev = newprev;
  n.val = cur.val;
  newprev.next = n;

  newprev = n;
  copy_while(cur.next, n, newprev);
  }
}

dllist copy(dllist l)
  requires true
  ensures true;
 {
  //dllist* nil = NULL;  // To make graphs easier to follow.
  dllist curr;

  dllist newprev;
  dllist _new;
  dllist result;

  //  _spec_assume("def_checker(dllist,dllist,96)" );
  //_spec_assume("add_edge(kind_C[(l) =dllist((nil))=>])");

  curr = l;

  if (curr != null) {
    newprev = null;
    _new = malloc();
    _new.next = null;
    _new.prev = newprev;
    _new.val = curr.val;
    result = _new;
    newprev = _new;

    copy_while (curr, _new, newprev);

    return result;
  }
  else {
    return null;
  }
}
