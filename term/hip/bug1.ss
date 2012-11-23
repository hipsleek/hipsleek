data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
	inv n >= 0;

int length (node xs)
 requires xs::ll<n>
 case {
  xs=null -> variance [0] ensures n=0 & res=0; // fails without n=0!
  xs!=null -> variance [1,n] ensures xs::ll<n> & res=n;
 }
{
  if (xs==null) return 0;
  else {
         node tmp = xs.next;
         int r = 1+length(tmp);
         //dprint;
         return r;
  }
}
/*
Termination checking result:
bug1.ss_21_19: Terminating: The given variance is well-founded.
bug1.ss_21_19: Terminating: The given variance is well-founded.
bug1.ss_21_19: Unreachable state.
*/


