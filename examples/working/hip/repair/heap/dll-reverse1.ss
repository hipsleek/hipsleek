data node {
	node prev;
	node next;	
}

dll<p,n> == self = null & n = 0 
  or (exists q: self::node<p , q> * q::dll<self, n-1> & n > 0);

lseg<p, q, n> == self = q & n = 0 
or self::node<p, u> * u::lseg<self, q,n-1> & n > 0;

node reverse(node x)
case {
   x= null -> ensures res = null;
   x != null -> requires x::lseg<p, y, n> * y::node<_,null> & p = null
   ensures y::lseg<q, x, n> * x::node<_,null> & res = y & q = null;
}
{
  if (x==null){
     return null;
   }
  else if (x.next == null){
     return x;
  }
  else {
     node k;
     // dprint;
     k = reverse(x.next);
     x.next.next = x;
     x.prev = x.next;
     x.next = null;
     // return k.next;
     return k;
  }
}
