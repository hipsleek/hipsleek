/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<"n":n,"l":S> == self = null & [
                                   "n": n=0;
                                   "l": S={}
                                  ]
  or self::node<v, r> * r::ll<n1,S2> & 
   ["n": n=1+n1;
    "l": S = union({v},S2)
    ]
  inv true & ["n":n>=0] ;

/* append two singly linked lists */
void append(node x, node y)

  requires x::ll<n1,L1> * y::ll<n2,L2> & ["n":n1>0]
    // & x!=null 
  ensures x::ll<r, L> & ["n":r=n1+n2; 
                         "l":L = union(L1,L2)
                         ] ;

{
	if (x.next == null) {
		x.next = y;
	} else {
		//assume false;
		append(x.next, y);
	}
}

