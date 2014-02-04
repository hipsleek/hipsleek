data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q>*q::ll<n-1>
  inv n>=0;

ls<p,n> == self=p & n=0
  or self::node<q>*q::ls<p,n-1> & self!=p
  inv n>=0;

void loop(node@R l1, node@R l2) 
  requires l2::ls<p,n> * l1::ls<q,n> * p::node<null> 
  ensures l2::ls<p,n> * l1::ls<q,n> * p::node<null> & l2'=p & l1'=q;
{
  l2= l2.next;
  if (l2==null) return;
  else {l1=l1.next;
    loop(l1,l2);
  };
}
