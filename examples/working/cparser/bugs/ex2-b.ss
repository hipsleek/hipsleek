
data node {
  int val;
  node next;
}

/*@
ll<> == self=null
  or self::node^<_,p>*p::ll<>;
*/


/* HeapPred H( node a). */
/* HeapPred G( node a). */


void foo(node x)
 /* infer [H,G] */
 /*  requires H(x) */
 /* ensures  G(x); */
 {
   if (x != null) {
     foo(x.next);
   }
   return;
 }

