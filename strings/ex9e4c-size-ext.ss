data node {
	int val;
	node next;
}


pred_extn size[R]<k> ==
   k=0 // base case
   or R::size<i> & k=1+i // recursive case
  inv k>=0;

/* view for a singly linked list */
ll<> == self = null
	or self::node<_, q> * q::ll<>
  ;
ll_one<> == self::node<_, q> * q::ll<>;

ll_oneN<n> == self::node<_, q> * q::lln<n1> & n1>=0 & n=n1+1
  inv n >= 1;

lln<n> == self = null & n = 0
	or self::node<_, q> * q::lln<n-1>
  inv n >= 0;

HeapPred H(node a).
HeapPred G(node a).

relation P(int a).
relation Q(int a, int b).

int size_helper(node x)

  infer [@size,@post_n]
  requires x::ll_one<> ensures x::ll_one<> ;

/*
 infer [@post_n] 
 requires x::ll_oneN<n> ensures x::ll_oneN<m> ;
*/
{
  if (x.next==null)
    return 1;
  else {
    return size_helper(x.next) + 1;
  }
}
