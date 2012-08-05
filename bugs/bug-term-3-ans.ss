data node {
  int val;
  node next;
}

// list segment of n nodes
lseg<p,n> == self=p & n=0
  or self::node<v, q> * q::lseg<p,n-1>
  inv n>=0;


// circular linked-list of nodes
clist<n> == self::node<v, q> * q::lseg<self,n-1>
  inv n>=1 ;

node append(node x, node y)
  requires x::lseg<null,n> & Term[n]
  ensures  res::lseg<y,n>;
  requires x::lseg<null,n> & x=y & n>0 & Term[n] 
  ensures res::clist<n>;
{
  if (x==null) {
    return y;
  } else {
    x.next = append(x.next,y);
    return x;
  }
}



