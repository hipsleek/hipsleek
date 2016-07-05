data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
	or self::node<_, r> * r::cll<p, n-1> & self != p  
	inv n >= 0;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::cll<self, n-1>  
	inv n >= 0;

HeapPred H(node a, node b).
HeapPred G(node a, node b).

/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node h)

   infer [H,G] 
   requires H(rest,h)
   ensures G(rest,h);
/*
	requires rest::cll<p, n> & h = p 
	ensures rest::cll<p, n> & res = n; 
*/

{
  int n;
  if (rest == h)
    return 0;
  else {
    n = count_rest(rest.next, h);
    n = n + 1;
    return n;
  }
}

/*
# cll.ss

 H(rest,h)&h!=rest --> rest::node<val_36_824,next_36_825>@M * 
  HP_6(next_36_825,h@NI) * HP_7(h,rest@NI)&true,

 HP_6(next_36_825,h@NI) * HP_7(h,rest@NI)&h!=rest 
   --> H(next_36_825,h)&true,

 H(rest,h)&h=rest --> G(rest,h)&true,

 rest::node<val_36_824,next_36_825>@M * G(next_36_825,h)&
  h!=rest --> G(rest,h)&true]

3rd RelAssume is a candidate for splitting, as it is
complementary to 1st RelAssume

*/
