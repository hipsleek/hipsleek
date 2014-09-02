UTPre@length fpre(int n).
UTPost@length fpost(int n).

data node { node next; }

ll<n> == self = null & n = 0 or
  self::node<p> * p::ll<n-1>
  inv n >= 0;
  
int length (node x)
  infer [@term]
  requires x::ll<n> & fpre(n)
  ensures x::ll<n> & res = n & fpost(n);
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}
