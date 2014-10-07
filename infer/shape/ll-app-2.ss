data node {
  int val;
  node next;
}

ll<> == self = null
	or self::node<_, q> * q::ll<> 
  inv true;

ll1<n> == self = null & n=0
	or self::node<_, q> * q::ll1<n-1>
  inv n>=0;

ll2<n, sm, lg> == self = null & n = 0 & sm <= lg 
  or (exists qs: self::node<sm, q> * q::ll2<n-1, qs, lg> & sm <= qs)
  inv n >= 0 & sm <= lg;

void append(node x, node y)
  requires true
  ensures true;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
