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
     k = reverse(x.next.next);
     // dprint;
     // k = reverse(x.next);
     // dprint;
     x.next.next = x;
     x.next = null;
     return k;
  }
}

// x'::node<u_2000> * y::node<flted_11_101> * u_2000::lseg<y,flted_6_1999>&
// flted_11_101=null & x'=x & flted_6_1999=n-1 & u_2000!=null & x!=null & 1<=n
// ~>
// x::node<u_2000> * k'::lseg<u_2000,n_2012> * u_2000::node<flted_12_2019>&
// flted_12_2019=null & y=k' & n=n_2012+1 & x'=x & 0<=n_2012 & x!=null & 
// u_2000!=null

// (exists nxt77,nxt79_11677. nxt77->node{nxt79_11677} * x'->node{nxt77} & flt28=0 & k'=p427 & y=p427 & x=x' & flt92=nil & n-1=0)