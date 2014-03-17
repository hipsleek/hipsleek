data node {
  int val;
  node next;
}

HeapPred H(node a).
  HeapPred G(node a, node b).

  HeapPred H1(node a).
  HeapPred G1(node a, node b).

  node insert (node list, int d, int position)
  infer[H,G]
  requires H(list)
     ensures G(list,res);//'
{
  node prev_list;
  node tmp_list;
  node new_list;

  new_list = new node(d, null);

  if (list == null)
    {
      return new_list;
    }

  prev_list = null;
  tmp_list = list;

  while (tmp_list != null && position > 0)
    infer[H1,G1]
      requires H1(tmp_list)
      ensures G1(tmp_list,tmp_list');//'
    {
      prev_list = tmp_list;
      tmp_list = tmp_list.next;
      position = position - 1;
    }

  new_list.next = prev_list.next;
  prev_list.next = new_list;

  return list;
}
