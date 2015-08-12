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


lln<n> == self = null & n = 0
	or self::node<_, q> * q::lln<n-1>
  inv n >= 0;

HeapPred H(node a).
HeapPred G(node a).

relation P(int a).
relation Q(int a, int b).

int size_helper(node x)
/*
  infer[H,G]
  requires H(x) //0<=m
  ensures  G(x);// & SIZEH(res,n);//res=m+n & m>=0
*/
//infer[@shape]  requires true ensures true;
//  infer [P,Q]  requires x::lln<n> & P(n)  ensures x::lln<n> & Q(n,res);
  infer [@size,@post_n]  requires x::ll<>  ensures x::ll<> ;
//  infer [@pre_n,@post_n]  requires x::lln<n>  ensures x::lln<n> ;
//  infer[@shape,@size]  requires true ensures true;
{
  if (x==null)
    return 0;
  else {
    return size_helper(x.next) + 1;
  }
}
