
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
    bind x to (xnext, xp1, xp2) in {
    if (nondet ()) xp2 = xp1;
    else xp2 = new dnode(0);

    //dprint;
    return trav (xnext);
    }
  }
}
