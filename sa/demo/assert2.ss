data node {
 int val;
 node left;
 node right;
}

HeapPred H(node x).
PostPred G(node x).

int mark(node x) 
/*
 requires x::node<a,b,c> 
 ensures x::node<a,b,c> & res=1;
*/
 requires x::node<a,_,r> * H(r)
 ensures x::node<a,_,r> * H(r) & res=a;
{
  int ttt= x.val;
  return ttt;
}

/*
# assert2.ss

 we could give a warning but should allow uninterpreted heap
 predicates in specification

Last Proving Location: 1 File "assert2.ss",Line:10,Col:0

ERROR: at _0:0_0:0 
Message: error 3: free variables [H] in proc mark 
 Stop Omega... 26 invocations Halting Reduce... 
caught
(Program not linked with -g, cannot print stack backtrace)

*/
