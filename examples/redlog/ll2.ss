data node {
    int val;
    node next;
}
ll<n, s> == self = null & n = 0 & s = 0 or
            self::node<p, q> * q::ll<n1, s1> & n = n1 + 1 & s = s1 + p & p >= 0
            inv n >= 0 & s >= 0;

void mult(node x, int a)
  requires x::ll<n, s> & x != null & a >= 0
  ensures x::ll<n, s*a>;
{
  x.val = x.val * a;
  if (x.next != null) {
    mult(x.next, a);
  }
}

void add(node x, int a)
  requires x::ll<n, s> & x != null & a >= 0
  ensures x::ll<n, s+a*n>;
{
  x.val = x.val + a;
  if (x.next != null) {
    add(x.next, a);
  }
}

int length(node x)
  requires x::ll<n, s>
  ensures res = n;
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}

/*
void add2(node x, int a)
  requires x::ll<n, s> & x != null
  ensures x::ll<n, s+a*n>;
{
  int n = length(x);
  x.val = x.val + n*a;
}
*/
