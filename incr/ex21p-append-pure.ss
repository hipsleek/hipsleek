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

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;


HeapPred P(node x, node y).


node append(node x, node y)
  requires x::ll<>
  ensures res::lseg<y> 
    & (res=y & x=null | res=x & x!=null)
  ;
{    
  if (x==null) return y;
  else {
      x.next = append(x.next, y);
      return x;
  }
}


/*
# ex21p.ss
 node append(node x, node y)
  requires x::ll<>
  ensures res::lseg<y> 
    & (res=y & x=null | res=x & x!=null)
  ;


******************************
   ******* SPECIFICATION1 ********
******************************
 infer[@leak HP_1620,HP_1621]requires HP_1620(x) * HP_1621(y)&
truerequires emp&MayLoop[]
 ensures htrue&true{,(4,5)=__norm#E};

# Is there a reason why we change P(x,y) to HP(x) * HP(y), and moreover
 without any warning. Can we not support P(x,y) directly, if needed?


*/
