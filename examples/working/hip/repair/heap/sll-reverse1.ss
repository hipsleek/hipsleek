data node {
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<q> * q::ll<n-1> 
  inv n >= 0;

node reverse(node xs)
	requires xs::ll<n>
	ensures res::ll<n>;
{
  if (xs == null) return null;
  else {
     if (xs.next == null) return xs;
     else {
         node tmp;
         tmp = reverse(xs.next);
         tmp.next = xs;
         xs.next = null;
         return xs;
     }
  }
}