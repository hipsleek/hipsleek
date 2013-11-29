// linked-list
data node {
  int x;
  node next;
}

data node_star {
  node deref;
}

ll<n> == self=null & n=0
   or self::node<_,q>*q::ll<n-1>
   inv n>=0;

/*
 defn above when using node_star is somewhat unnatural
 A more accurate one is to use:
      node_star t = &q.deref.next;
      return 1+foo(t);
 However, this may require us to support ptr arithmetic
 and ability to handle field access.
      q.deref::node<v,n> 
      q.deref.node.val::<v>*q.deref.node.next<n>

*/

int foo(node_star@C q)
  requires q::node_star<r>*r::ll<n>
  ensures q::node_star<r>*r::ll<n> & res=n;
{
  if (q.deref==null) return 0;
  else {
      node_star t = new node_star(q.deref.next);
      return 1+foo(t);
  }
}


int foo2(node val_q)
  requires val_q::ll<n>
  ensures val_q::ll<n> & res=n;
{
  if (val_q==null) return 0;
  else return 1+foo2(val_q.next);
}

