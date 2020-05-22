data node {
  int val;
  node next;
}

ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2
  inv n >= 0;

void insert(node x, int a)
  requires x::ll<n> & n > 0
	ensures x::ll<n+1>;
{
  if (x.next == null){
    x.next = new node(a, null);
  }
  else insert(x.next, a);
}
