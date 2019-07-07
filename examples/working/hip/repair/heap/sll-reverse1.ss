data node {
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<q> * q::ll<n-1>  & n > 0
  inv n >= 0;

node reverse(node xs)
  requires xs = null ensures res = null;
  requires xs::ll<n> & xs != null
  ensures xs::ll<n-1> & res::node<null> & xs.next = res;
{
  if (xs == null) return null;
  else {
     // node tmp;
     // tmp = reverse(xs.next);
     // if (tmp != null) tmp.next = xs;
     // xs.next = null;
     // return tmp;
     if (xs.next == null) return xs;
     else {
         node tmp;
         // dprint;
         tmp = reverse(xs.next);
         // dprint;
         tmp.next = xs;
         xs.next = null;
         return xs;
     }
  }
}