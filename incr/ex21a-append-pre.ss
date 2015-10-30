/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null
	or self::node<_, q> * q::ll<> 
  inv true;

	
HeapPred P(node x, node y).


void append(node x, node y)
  infer [P,@classic]
  requires P(x,y)
  ensures true ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append(x.next, y);
}


/*
# ex21a.ss

  infer [P,@classic]
  requires P(x,y)
  ensures true ;

******************************
   ******* SPECIFICATION1 ********
******************************
 infer[@leak HP_1620,HP_1621]requires HP_1620(x) * HP_1621(y)&
truerequires emp&MayLoop[]
 ensures htrue&true{,(4,5)=__norm#E};

# Is there a reason why we change P(x,y) to HP(x) * HP(y), and moreover
 without any warning. Can we not support P(x,y) directly, if needed?


*/
