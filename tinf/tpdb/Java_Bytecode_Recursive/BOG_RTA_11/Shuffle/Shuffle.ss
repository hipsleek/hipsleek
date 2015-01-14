data node { int value; node next; }

ll<n> ==
  self = null & n = 0 or
  self::node<v, p> * p::ll<n-1>
  inv n >= 0;

node reverse (node l)
{
  if (l == null || l.next == null) return l;
  node nextItem = l.next;
  node reverseRest = reverse(nextItem);
  l.next = null;
  nextItem.next = l;
  return reverseRest;
}

node shuffle (node xs) 
{
  if (xs == null)
    return null;
  else {
    node next = xs.next;
    return new node(xs.value, shuffle(reverse(next)));
  }
} 
