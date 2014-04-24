data node { int value; node next; }

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p>
  inv n >= 0;

/*
// Binding error at (1)
node reverse (node l)
  requires l = null
  ensures res = null;
{
  if (l == null || l.next == null) return l; // (1)
  node nextItem = l.next;
  node reverseRest = reverse(nextItem);
  l.next = null;
  nextItem.next = l;
  return reverseRest;
}
*/

node reverse (node l)
  requires l = null
  ensures res = l;  
  
  requires l::node<_, null>@L
  ensures res = l;
  
  requires l::node<_, p> * p::node<_, q> * q::lseg<n, null>
  case {
    q = null -> ensures p::node<_, l> * l::node<_, null> & res = p;
    q != null -> ensures res::lseg<_, _> * p::node<_, l> * l::node<_, null>;
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
