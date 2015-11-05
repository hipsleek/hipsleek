/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next#REC;	
}


/* view for a singly linked list */
/*
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;
*/
ll<> == self = null 
	or self::node<_, q> * q::ll<> 
  inv true;

/*
lseg<p> == self = p
	or self::node<_, q> * q::lseg<p> & self != p
  inv true;
*/

lseg2<p> == self = p
	or self::node<_, q> * q::lseg2<p> 
  inv true;

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
   inv k>=0;

HeapPred P(node x, int@NI i).

int search(node x, int i)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
  infer [P,@classic,@pure_field]
  requires P(x, i)
  ensures false;
{    
  if (x==null) return 0;
  else { 
    if (x.val == i) return 1;
    else {
      int r = search(x.next, i);
      return r;
    }
  }
}

/*
# ex20e8.ss 

[ // BIND
(2;0)P(x,i@NI)&
x!=null --> x::node<val_48_1602,next_48_1603>@M * 
            HP_1604(val_48_1602@NI,i@NI,x@NI) * 
            HP_1605(next_48_1603,i@NI,x@NI)&
true,
 // PRE_REC
(2;2;0)HP_1604(val_48_1602@NI,i@NI,x@NI)&val_48_1602!=i & x!=null --> emp&
true,
 // PRE_REC
(2;2;0)HP_1605(next_48_1603,i@NI,x@NI) * x::node<val_48_1602,next_48_1603>@M&
val_48_1602!=i --> P(next_48_1603,i@NI)&
true,
 // POST
P(x,i@NI)&true --> htrue&
x!=null]

Procedure search$node~int SUCCESS.


*/
