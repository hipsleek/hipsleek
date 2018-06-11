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


/*
Checking procedure length$node...

Post condition cannot be derived:
(may) cause: [  (must) cause:  n=1+n2_1927 & res=n2_1927+2 |-  res=n. LOCS:[9;17;0;13] (must-bug),valid]

Context of Verification Failure: repair-ex.ss_13:8_13:26

Last Proving Location: repair-ex.ss_17:18_17:36

ERROR: at repair-ex.ss_13:8_13:26
Message: Post condition cannot be derived.

Procedure length$node FAIL.(2)
*/
