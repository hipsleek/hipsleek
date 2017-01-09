UTPre@length fpre(int n).
UTPost@length fpost(int n).

data node {
  int val;
  node next;
}

lseg<n, p> ==
  self = p & n = 0 or
  self::node<_, q> * q::lseg<n-1, p>
  inv n>=0;

clist<n> ==
  self::node<_, q> * q::lseg<n-1, self>
  inv n>0;

lemma self::clist<n> <- self::lseg<n-1, q> * q::node<_, self>;

int length (node x)
  infer [@term]
  //requires x::lseg<n, null>@L & fpre(n)
  //ensures res=n & fpost(n);

  requires x::clist<n>@L & fpre(n)
  ensures fpost(n);
{
  if (x == null)
    return 0;
  else
    return 1 + length(x.next);
}
