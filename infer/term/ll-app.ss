data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
     or self::node<_, r> * r::cll<p, n-1> //& self != p  
	  inv n >= 0;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::cll<self, n-1>  
	inv n >= 0;

void append(node x, node y)
  requires x::cll<null,n> & n>0 & Term[n]
  ensures x::cll<y,n> ;
  requires x::cll<null,n> & x=y & n>0 & Term[n]
  ensures x::hd<n> ;
  requires x::ll<n>*y::ll<m> & n>0 & Term[n]
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
