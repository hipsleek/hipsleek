// linked-list
data node {
  int x;
  node next;
}

data node_star {
  node deref;
}

ll<n>== self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

int foo(node_star@C q)
  requires q::node_star<r>*r::ll<n>
  ensures q::node_star<r>*r::ll<n> & res=n;
{
  if (q.deref==null) return 0;
  else return 1+foo(&q.deref.next);
}


int foo2(node q)
  requires q::ll<n>
  ensures q::ll<n>;
{
  if (q==null) return 0;
  else return 1+foo2(q.next);
}

