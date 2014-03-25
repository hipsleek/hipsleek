data cell {
  int val;
}

HeapPred H(cell a,cell b).
PostPred G(cell a,cell b).

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


 // BIND
(1;0)H(p,q) & p=null --> q::cell<val>@M,
 // BIND
(2;0)H(p,q) & p!=null --> p::cell<val>@M * HP_907(q,p@NI),
 // POST
(1;0)q::cell<val>@M & p=null --> G(p,q),
 // POST
(2;0)HP_907(q,p@NI) * p::cell<val>@M --> G(p,q)]


======
# err3.ss

WHY HP_907 became HP_934???

[ H(p,q) ::= 
 q::cell<val>@M&p=null
 or p::cell<val1>@M * HP_934(q,p)
 ,
 G(p,q) ::= 
 p::cell<val>@M * (htrue)
 or q::cell<val1>@M&p=null
 ,
 HP_934(q,p) ::= NONE]

*/
