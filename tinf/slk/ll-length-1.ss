UTPre@fact fpre(node x).
UTPost@fact fpost(node x).

data node { node next; }

ll<n> == self = null & n = 0 or
  self::node<p> * p::ll<n-1>
  inv n >= 0;
  
int length (node x)
  infer [@term]
  requires x::ll<n> & fpre(x)
  ensures x::ll<n> & res = n & fpost(x);
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}
