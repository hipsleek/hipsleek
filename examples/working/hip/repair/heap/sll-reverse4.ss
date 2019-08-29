data node {
  node next;	
}

lseg<p,n> == self = p & n = 0 
or self::node<u> * u::lseg<p,n-1> & n > 0;

node reverse(node x)
case {
   x= null -> ensures res = null;
   x != null -> requires x::lseg<y, n> * y::node<null>
   ensures y::lseg<x, n> * x::node<null> & res = y;
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
     k = reverse(x.next);
     x.next.next.next = x;
     x.next = null;
     return k;
  }
}

