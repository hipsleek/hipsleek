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

void create_while(ref dllist l)
  infer[H1,G1]
  requires H1(l)
  ensures G1(l');//'
{
  dllist n;
   n = malloc();
   if (n==null) {
     return;
   }
    n.next = l;
    n.prev = null;
    n.val = 0;
    l.prev = n;

    l = n;
    create_while (l);
}

HeapPred G2(dllist a).

dllist create()
   infer[G2]
  requires true
  ensures G2(res);//'
  {
    // dllist nil = null;  // To make graphs easier to follow.
  dllist l;
  
  l = malloc();
  if (l==null) return null;
  l.next = null;
  l.prev = null;
  l.val = 0;

  create_while(l);

  return l;
}
