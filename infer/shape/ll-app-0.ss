data node {
  int val;
  node next;
}

ll<> == self = null
	or self::node<_, q> * q::ll<> 
  inv true;

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
