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
  infer[H,H1]
  requires H(x)  ensures H1(x);
*/

  infer[@shape_post] 
  requires x::node<_, null> or x=null
  ensures true;


{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14b.ss

  infer[@shape_post] 
  requires x::sll<>
  ensures true;

For @shape_post, we need to simplify the base-case:

[ GP_1636(x_1663) ::= x_1663::node<Anon_1664,q_1651>@M * GP_1636(q_1651)
 or x_1663::sll<>@M&x_1663=null
 (4,5)]

# EXPECTS:

[ GP_1765(x_1792) ::= 
   x_1792::node<Anon_1793,q_1780>@M * GP_1765(q_1780)
   or x_1792=null(4,5),

# Maybe can add this to post_synthesis

1:43:iprocess_action inp1 :infer_dangling
1:57:iprocess_action inp1 :split_base
1:71:iprocess_action inp1 :post_synthesize
1:85:iprocess_action inp1 :norm_seg
1:99:iprocess_action inp1 :partition (pre, pre-oblg, post, post-oblg)
1:113:iprocess_action inp1 :seq:[(0,infer_dangling),(0,split_base),(0,partition (pre, pre-oblg, post, post-oblg))]

*/

