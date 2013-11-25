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
  if (p==null) {
    int i = p.val;
    return i;
  } else return -1;
}

/*
# err.ss

Obtain:
[ // BIND
 H(p)&p=null --> hfalse& false,
  // POST
 H(p)& p!=null --> G(p)]

I think we still need to split to first obtain:
(see err-1b-split.slk)

 H(p)&p=null --> hfalse& false,
 H(p)& p!=null --> H_3(p)

 H_3(p) & p!=null --> G(p)
 H_3(p) := htrue

After that, we can derive:

 H(p) ::= H_3(p) & p!=null
 G(p) ::= H_3(p) & p!=null
 H_3(p) ::= htrue

where H_3(p) is a dangling reference

*/
