data node {
  int val;
  node_star next;
}

data node_star {
  node pdata;
}

ll<n> == self = null & n = 0 
  or self::node_star<p> * p::node<_,q> * q::ll<n1> & n = n1 + 1
  inv n >= 0;

/* insert an item to the end of current list */
void insert_last(node_star x, int a)
  requires x::ll<n> & n > 0
  ensures x::ll<n+1>;
{
  if (x.pdata.next == null)
  {
    node p = new node (a, null);
    node_star y = new node_star(p);
    x.pdata.next = y;
  }
  else
  {
    insert_last(x.pdata.next, a);
  }
}


void delete_last(node_star x)
  requires x::ll<n> & n > 1
  ensures x::ll<n-1>;
{
  if (x.pdata.next.pdata.next == null)
    x.pdata.next = x.pdata.next.pdata.next;
  else
    delete_last(x.pdata.next);
}
