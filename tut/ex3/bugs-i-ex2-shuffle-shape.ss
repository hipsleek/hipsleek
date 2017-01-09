data node { int value; node next; }

node reverse (node l)
  infer[@shape,@post_n,@term]
  requires true
  ensures true;
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
  infer[@shape,@post_n,@term]
  requires true
  ensures true;
{
  if (xs == null)
    return null;
  else {
    node next = xs.next;
    return new node(xs.value, shuffle(reverse(next)));
  }
} 
