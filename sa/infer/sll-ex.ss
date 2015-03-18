
data dnode { int d}

data node {
  node next;
  dnode p1;
  dnode p2;
}

HeapPred H(node a).
HeapPred G(node a).


bool nondet ()
  requires true ensures true;

void trav(node x)
  infer [H,G] requires H(x)
     ensures G(x);
{
  if (x == null) return;
  else {
    if (nondet ()) x.p2 = x.p1;
    else x.p2 = new dnode(0);

    //dprint;
    return trav (x.next);
  }
}
