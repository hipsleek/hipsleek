data cell {
  int val;
}

HeapPred H(cell a).
HeapPred G(cell a).

int foo(cell p)
  infer [H,G]
  requires H(p)
  ensures G(p);
{
  if (p!=null) {
    int i = p.val;
    //dprint;
    goo(p);
    return i;
  } 
  else return -1;
}

void goo(cell p)
  requires p=null
  ensures true;

/*
# err2a.ss : 

currently fails.

If we could infer H(p) ::= p=null, it would
be more comprehensive.


*/
