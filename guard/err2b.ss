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
    dispose(p);
    int j = p.val;
    return j;
  } 
  else return -1;
}

void dispose(cell p)
  requires p::cell<_>
  ensures true;

/*
# err2b.ss : 

Why did this failure lead to shape analysis
but not err2a.ss

If we could infer H(p) ::= p=null, it would
be more comprehensive.
*************************************
*******relational assumptions (4) ********
*************************************
[ // BIND
(1;0)H(p)&
p!=null --> p::cell<val>@M]

Procedure foo$cell result FAIL.(1)

*************************************
*******relational definition ********
*************************************
[ H(p) ::= p::cell<val>@M]
*************************************


*/
