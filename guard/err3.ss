data cell {
  int val;
}

HeapPred H(cell a,cell b).
  HeapPred G(cell a,cell b).

  int foo(cell p,cell q)
  infer [H,G]
  requires H(p,q)
     ensures G(p,q);
{
  if (p==null) {
    int i = q.val;
    return i;
  } else {
    return p.val;
  }
}


/*
# err2.ss : The message here is not very good.
  Should we perhaps infer a false here?

 // BIND (1;0)

H(p,q)&p=null --> q::cell<val>@M * HP_902(p,q@NI),
 // no need for HP_902(p,..)

 // BIND(2;0)
H(p,q)&p!=null --> p::cell<val>@M * HP_908(q,p@NI),

 // POST(1;0)

q::cell<val>@M & p=null --> G(p,q),
 // POST(1;0)

HP_902(p,q@NI)& p=null --> emp,

 // POST(2;0)

HP_908(q,p@NI) * p::cell<val>@M --> G(p,q)]

# why did we rename HP_908 to HP_939?
  It does not seem necessary.
======

 H(p,q) ::= 
 p::cell<val>@M * HP_939(q,p)
 or emp&p=null
 ,
 G(p,q) ::= 
 p::cell<val>@M * (htrue)
 or q::cell<val1>@M&p=null
 ,

 HP_939(q,p) ::= NONE]

*/
