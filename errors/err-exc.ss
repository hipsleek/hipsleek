class NullPtrErr extends __Error {} 
//class NullPtrErr extends __Exc {} 
//class e2 extends __Exc {} 

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


 void foo1(node x) 
   requires x::ll<n> 
   ensures x=null & flow __Error 
        or x!=null & flow __norm; 
   {
      nonnull(x);
      dprint; 
       // a possible NullPtrError at Line (1)
      //assert x!=null; 
       // success or not?
      assert true; //'
      assert true & flow NullPtrErr;
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
    x=null -> 
       ensures true & flow NullPtrErr;
    x!=null -> 
       requires x::node<a,b>
       ensures x::node<a,b>;
   }

/*
void nonnull$node(  node x)
static  case {x=null -> EAssume (4, ):
                   true & true & {FLOW,(15,16)=__Exc,} ;
  x!=null -> exists [](I)[a;b][]x::node<a,b> & true & {FLOW,(13,14)=__norm,}
               EAssume (5, ):
                 EXISTS(a_37,b_38: x::node<a_37,b_38> & a_37=a & b_38=b &
                 {FLOW,(13,14)=__norm,})
  }
*/
