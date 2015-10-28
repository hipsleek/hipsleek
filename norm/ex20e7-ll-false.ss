/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next; //#REC;	
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

HeapPred P(node x).

int len_seg(node x)
  //infer [P,@classic,@pure_field,@size,@term]
  //infer [P#{size,sum},@classic,@pure_field]
  //infer [P#size,P#sum,@classic,@pure_field]
  infer [P,@classic,@pure_field]
  requires P(x)
  ensures false;
{    
  if (x==null) return 0;
  else { 
    node n = x.next;
    dprint;
    int r=len_seg(n);
    dprint;
    return 1+r;
  }
}

/*
# ex20e7.ss 

[ // BIND
(2;0)P(x)&
x!=null --> x::node<val_48_1587,next_48_1588>@M * 
            HP_1589(val_48_1587@NI,x@NI) * HP_1590(next_48_1588,x@NI)&
true,
 // PRE_REC
(2;0)HP_1589(val_48_1587@NI,x@NI)&x!=null --> emp&
true,
 // PRE_REC
(2;0)HP_1590(n',x@NI) * x::node<val_48_1587,n'>@M&true --> P(n')&
true,
 // POST
P(x)&true --> htrue& x!=null]



*/
