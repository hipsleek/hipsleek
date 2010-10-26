data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

 class e1 extends __Exc {} 

 void foo1(node x) 
   requires x::ll<n>
   ensures true; 
   {
      nonnull(x);
      dprint; 
       // a possible NullPtrError at Line (1)
      //assert x!=null; 
       // success or not?
      assert true; //'
      assert true & flow e1;
   }
/*

   requires x::ll<n>
   ensures true; 

 A bug since foo1 reported as success when it should fail.

 Procedure foo1$node SUCCESS

      assert true; //'
      assert true & flow NullPtrErr;

(7, ):assert (7, ):: true & true & {FLOW,(13,14)=__norm,} ;
(6, ):assert (6, ):: true & true & {FLOW,(15,16)=__Exc,} 
 // why isn't e1 reflected? instead __Exc was usesd..

*/

  void nonnull(node x)
   case {
    x=null -> ensures true & flow e1;
     x!=null -> requires x::node<a,b>
       ensures x::node<a,b>;
   }

