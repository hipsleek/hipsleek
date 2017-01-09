data node { int val; node next; }

ll<n> ==
  self = null & n = 0 or
  self::node<_, p> * p::ll<n - 1>
  inv n >= 0;

int length (node x) 
  requires x::ll<n>@L & Term[n]
  ensures res = n;
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}

int rand ()
  requires Term
  ensures true;

node double (node x, int i)
  requires x::ll<n>
  case {
    i >= n -> requires Term ensures res::ll<n>;
    i < n -> requires Term[n - i] ensures res::ll<2*n - i>;
  }
{
  if (i >= length(x)) 
    return x;
  else
    return double(new node(rand(), x), i + 2);
}
