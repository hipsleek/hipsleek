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





/* append two singly linked lists */
int append2(int x, int y)
  infer [@term]
  requires x>0 & y>=0 
  ensures res=x+y;
{    
	if (x == 1) 
          return 1+y;
	else
          return 1+append2(x-1, y);
}

/*
# num-app.ss

  infer [@term]
  requires x>0 & y>=0 
  ensures true ;

case analysis here seems better than ll-app.ss. Why?

append2:  requires emp & 0<x & 0<=y
  case {
     x=1 & 0<=y -> 
       requires emp & Term[8,1]
       ensures emp & true; 
     2<=x & 0<=y -> 
       requires emp & Term[8,2,-1+(1*x)+(0*y)]
       ensures emp & true; 
     }

 */




