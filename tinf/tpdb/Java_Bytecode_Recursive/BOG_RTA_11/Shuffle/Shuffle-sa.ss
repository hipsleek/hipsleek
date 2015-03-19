data node { int value; node next; }

HeapPred G(node a).
HeapPred H(node a, node b).

node reverse (node l)
infer[G,H]
requires G(l)
ensures H(l, res);
{
  if (l == null || l.next == null) return l;
  node nextItem = l.next;
  node reverseRest = reverse(nextItem);
  l.next = null;
  nextItem.next = l;
  return reverseRest;
}

