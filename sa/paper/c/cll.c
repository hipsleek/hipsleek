struct node {
  int val; 
  struct node* next;	
};

/* view for singly linked circular lists */
/*@
clls<p, n> == self = p & n = 0
	or self::node<_, r> * r::clls<p, n-1> & self != p  
	inv n >= 0;

cll<p> == self = p
	or self::node<_, r> * r::cll<p> & self != p  
	inv true;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::clls<self, n-1>
	inv n >= 0;
*/
/*@
HeapPred H(node a, node b).
HeapPred G(node a, node b).
*/
/* functions to count the number of nodes in a circular list */
int count_rest(struct node* rest, struct node* h)
/*@
   infer [H,G] 
   requires H(rest,h)
   ensures G(rest,h);
*/
/*
	requires rest::cll<p, n> & h = p 
	ensures rest::cll<p, n> & res = n; 
*/

{
  int n;
  if (rest == h)
    return 0; 
  else
    {
      n = count_rest(rest->next, h);
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
