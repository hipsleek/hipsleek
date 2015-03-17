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
