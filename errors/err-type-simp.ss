/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

	
   

 int sqrt(int v)
 case {
   v>=0 -> ensures res>=0;
   v<0 -> ensures true & flow __Error;
 }
 /* requires v>=0 */
 /* ensures res>=0; */
 /* requires v<0 */
 /* ensures true & flow __Error; */

 pos<> == self=null 
      or self::node<v,q> * q::pos<> & v>=0
      inv true;

 one_neg<> == self::node<v,q> * q::ll<_>  & v<0
    or self::node<v,q> * q::one_neg<> & v>=0
  inv self!=null;

// why is there a type-error below when res is used?

 int sumsqrt(node x)
   /* requires x::pos<> */
   /* ensures  res>=0 ; */
   /* requires x::one_neg<> */
   /* ensures  true & flow __Error; */
   requires x::ll<_> 
   ensures  res>=0 & flow __flow ; //type error here? why
{
  if (x==null) return 0;
  else return sqrt(x.val)+sumsqrt(x.next);
}



