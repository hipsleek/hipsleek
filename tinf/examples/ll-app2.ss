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

void append2(node x, node y)
  infer [@term]
  requires x::ll<n1> * y::ll<n2> & n1>0 & n2>=0
       // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2> ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

/*
# ll-app2.ss

  infer [@term]
  requires x::ll<n1> * y::ll<n2> & n1>0 
       // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2> ;

# added n2>=0 but extra base-case still present.

append2:  requires x::ll<n1> * y::ll<n2> & 0<n1 & 
0<=n2case {
      n1=1 & 
      1<=n2 -> requires emp & Term[7,1]
 ensures x::ll<flted_35_47> & flted_35_47=n2+
      n1; 
      n2=0 & 
      n1=1 -> requires emp & Term[7,2]
 ensures x::ll<flted_35_47> & flted_35_47=n2+
      n1; 
      0<=n2 & 2<=n1 -> requires emp & Term[7,3,0+(1*n1)+(0*
      n2)]
 ensures x::ll<flted_35_47> & flted_35_47=n2+n1; 
      }

append2:  requires x::ll<n1> * y::ll<n2> & 0<n1
  case {
     // missing case n2<0 is false
     // why did we have redundant case analysis?
     // isn't it already terminating when Term[x]
     n1=1 & 1<=n2 -> 
         requires emp & Term[7,1]
         ensures x::ll<flted_35_47> & flted_35_47=n2+n1; 
     n2=0 & n1=1 -> 
         requires emp & Term[7,2]
         ensures x::ll<flted_35_47> & flted_35_47=n2+n1; 
     0<=n2 & 2<=n1 -> 
         requires emp & Term[7,3,0+(1*n1)+(0*n2)]
         ensures x::ll<flted_35_47> & flted_35_47=n2+n1; 
  }
 */




