data node { int value; node next; }

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p>
  inv n >= 0;

ll<n> ==
  self = null & n = 0 or
  self::node<v, q> * q::ll<n-1>
  inv n >= 0;

lemma_safe self::lseg<n,r> <- self::lseg<m,q>*q::node<_,r> & n=m+1;

lemma_safe self::ll<n> <- self::lseg<n, null>;

node reverse (node l)
  infer[@term]
  requires l::ll<n>
  case {
    n<=1 -> ensures res::ll<n> & res=l;
    n>1 -> ensures res::lseg<n-1,l> * l::node<_,null>;
  }
{
  if (l == null) return l;
  if (l.next == null) return l;
  node nextItem = l.next;
  node reverseRest = reverse(nextItem);
  l.next = null;
  nextItem.next = l;
  return reverseRest;
}

node shuffle (node xs) 
  infer[@term]
  requires xs::ll<n>
  ensures res::ll<n>;
{
  if (xs == null)
    return null;
  else {
    node next = xs.next;
    return new node(xs.value, shuffle(reverse(next)));
  }
} 
