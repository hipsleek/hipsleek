/* singly linked lists */

/* representation of a node */
data node {
	node next
}

ll<n> == self=null & n = 0
or self::node<r> * r::ll<n2> & n = n2 + 1;

int length(node x)
requires x::ll<n>
ensures x::ll<n> & res = n;
{
   if(x==null) return 1;
     else {
          int n = 1 + length(x.next);
          return n;
     }
}
