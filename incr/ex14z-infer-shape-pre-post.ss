/* singly linked lists */
//../hip ex14-infer-shape-pre-post.ss --classic
/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).


int size_helper(node x)
/*
  infer[H]
  requires H(x)  ensures true;//H1(x);
*/
  infer[@shape_prepost] requires true ensures true;

{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14.ss

For @shape_post, we need to simplify the base-case:

[ GP_1765(x_1792) ::= x_1792::node<Anon_1793,q_1780>@M * GP_1765(q_1780)
 or x_1792::sll<>@M&x_1792=null
 (4,5),
 HP_1636(x_1663) ::= x_1663::sll<>@M(4,5)]

# EXPECTS:

[ GP_1765(x_1792) ::= 
   x_1792::node<Anon_1793,q_1780>@M * GP_1765(q_1780)
   or x_1792=null(4,5),
 HP_1636(x_1663) ::= x_1663::sll<>@M(4,5)]

*/

