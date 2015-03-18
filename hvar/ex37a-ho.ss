/*

  Description: fairly complicated inter-procedural passing 
  of stack variables between concurrent threads

 */
pred_prim Thrd{+%Q@Split}<>;
pred_prim dead<>;

HeapPred H().


void join3(Thrd t)
  requires t::Thrd{+ %H}<>
  ensures %H * t::dead<>;

void join2(Thrd t)
  requires t::Thrd{+ H()}<>
  ensures H() * t::dead<>;

/*
# ex37a.ss (join2)

!!!WARNING : uninterpreted free variables [H] in specification.Stop Omega... 33 invocations 

How do we distinguish var from H?

How about use H for type-inferencing, and convert
to HVar subsequently, when we manage to recognize?

*/
