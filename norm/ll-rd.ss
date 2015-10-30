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

	
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

HeapPred H(node x, node@NI y).

void append3(node x, node y)
/*
  infer [@shape_pre,@classic]
  requires true
  ensures true;
*/
  infer [H,@classic]
  requires H(x,y)
  ensures true;
{    
	if (x.next == null) 
           x.next = y;
	else
           append3(x.next, y);
}

/*
[ // BIND
(0)HP_1561(x,y)&
true --> x::node<val_32_1567,next_32_1568>@M * HP_1569(next_32_1568,y,x@NI)&
true,
 // PRE_REC
(2;0)HP_1569(next_32_1568,y,x@NI)&
next_32_1568!=null |#| x::node<val_32_1567,next_32_1568>@M&
true --> HP_1561(next_32_1568,y)&
true,
 // POST
(1;0)HP_1569(next_32_1568,y,x@NI)&
y'=y & x'=x & next_32_1568=null & next_33_1578=next_32_1568 --> emp&
true]

*/
