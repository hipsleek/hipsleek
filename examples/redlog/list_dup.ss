data node {
    int val;
    node next;
}

ll<n> == self = null & n = 0 or
         self::node<p, q> * q::ll<n1> & n = n1 + 1
         inv n >= 0;

node append(node x, node y)
  requires x::ll<n> * y::ll<m>
  ensures res::ll<n+m> * x::ll<n>;
{
  if (x == null) return y;
  else {
    node r = append(x.next, y);
    return new node(x.val, r);
  }
}

node product(node x, int b)
  requires x::ll<n> & b >= 0
  ensures res::ll<n*b> * x::ll<n>;
{
  if (b == 0) return null;
  else return append(x, product(x, b-1));
}
