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
  assume p=null;
  int i = p.val;
  return i;
}

/*
# err-1.ss

Obtained below, but how about
G(p)? Should we allow false to
be assumed?

[ // BIND
H(p)&p=null --> hfalse&
false]

Procedure foo$cell SUCCESS.

*************************************
*******relational definition ********
*************************************
[ H(p) ::= hfalse&false]


*/
