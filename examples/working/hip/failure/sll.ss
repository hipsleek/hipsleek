data node {
  int val;
  node next;
}

ls<y,n> == self=y & n = 0
  or self::node<_, r> * r::ls<y,n2> & n = 1 + n2;

int length(node x)
  requires x::ls<null,n>
  ensures x::ls<null,n> & res = n;
{
  if (x == null) return 0;
  else {
    int k;
    k = 1 + length(x.next);
    return k;
  }
}

node delete_first(node x)
  // requires x::ll<n> & n<=1 ensures res=null;
  requires x::node<a,t> * t::ls<null,n>
  ensures res::ls<null,n>;
  // requires x::ll<n> ensures res::ll<n>;
{
  if (x == null)
    return null;
  else if (x.next == null) {
    free(x);
    return null;
  }
  else {
    node y = x.next;
    free(x);
    return y;
  }
}

// node concat(node x, node y)
// {
//   if

// }

void main () {
  node x = new node(10, null);
  node y = new node(11, null);
  node z = new node(12, null);
  x.next = y;
  y.next = z;
  z.next = null;

  dprint;

  int n = length(x);
  dprint;
  assert (n = 3);

  // node y = delete_first(node x);
  // int m = length(y);
}
