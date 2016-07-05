/* insertion sort */

data node {
  int val; 
  node next; 
}

ll<n, a1, a2> ==   self = null & n = 0 or 
  self::node<_@a1,q@a2> * q::ll<n-1,a1,a2>
  inv n>=0;
  
     
  /* function to insert an element in a sorted list */
  node insert(node x, node y)
  requires x::ll<n,@L,@M> * y::node<_@L,null>
  ensures  res::ll<n+1, @A, @M> ; 
{
  if (x == null) return y;
  else {
    if (y.val <= x.val){
      y.next = x;
      return y;
    }else{
      node tmp;
      tmp = insert(x.next, y);
      x.next = tmp;
      return x;
    }
  }
}



/* insertion sort 
void insertion_sort(node x, ref node y)
  requires x::ll<n1, sm1, bg1> * y::sll<n2, sm2, bg2>
  ensures y'::sll<n1+n2, sm, bg> * x::bnd<n1, sm1, bg1> & sm <= sm2 & bg >= bg2;

{
	if (x != null)
	{
		y = insert(y, x.val);
		insertion_sort(x.next, y);
	}
}



*/










































