/* singly linked lists */
//../hip ex14-infer-shape-pre-post.ss --classic
/* representation of a node */
data node {
	int val;
	node next;
}

pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;

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

  relation R(int a,int b, int c).

int size_helper(node x)
/*
  infer[H]
  requires H(x)  ensures true;//H1(x);
*/
//  infer[@shape_prepost,@classic] requires true ensures true;
//  infer[@size,@post_n] requires x::sll<> ensures x::sll<>;
  infer[@post_n] requires x::ll<aa> ensures x::ll<bb>;

{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}

/*
# ex14k2.ss

  infer[@size,@post_n] requires x::sll<> ensures x::sll<>;

 EBase 
   exists (Impl)[size_1672]x::sll_size<size_1672>@M&MayLoop[]&
   {FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists size_1673: x::sll_size<size_1673>@M&
     res>=0 & size_1673>=res & size_1673=size_1672&{FLOW,(4,5)=__norm#E}[])

# Why did we not get res=size_1673?
  Below, we did obtain res=a

  infer[@post_n] requires x::ll<a> ensures x::ll<b>;

size_helper$node
 EBase 
   exists (Impl)[aa]x::ll<aa>@M&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists bb: x::ll<bb>@M&res>=0 & res=bb & res=aa&
     {FLOW,(4,5)=__norm#E}[])

*/


