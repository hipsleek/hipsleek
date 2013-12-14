struct node {
  int val;
  struct node * next;
}
/*@
HeapPred G2(struct node * a, struct node * b).
HeapPred H2(struct node * a,struct node * b).
*/

void append(struct node * x, struct node * y)
/*@
  infer[H2,G2]
  requires H2(x,y)
  ensures G2(x,y);
*/
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}
