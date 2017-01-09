data node {
  int val;
  node next;
}

node merge(node x, node y)
{
  node list = new node(1, null);
  node tmp = list;

  while (x != null && y != null)
    {
      if (x.val <= y.val)
        {
          tmp.next = x;
          tmp = tmp.next;
          x = x.next;
        }
      else
        {
          tmp.next = y;
          tmp = tmp.next;
          y = y.next;
        }
    }

  if (x == null)
    tmp.next = y;
  else
    tmp.next = x;

  return list.next;
}
