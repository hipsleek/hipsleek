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
H(p)&p!=null --> emp,
 // POST
(2;0)H(p)&p!=null --> G(p)]


How come we are missing on the following
relational assumption?

 <1>hfalse&false&{FLOW,(21,22)=__norm}[]
 inferred hprel: [H(p)&p=null --> hfalse&false]
[
*/
