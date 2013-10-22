data GList { int key;
  GList prev;
  GList next;
}

lseg<p> == self=p
  or self::GList<_,_,n> * n::lseg<p> & self!=null;

GList
 g_list_last (GList list)
  requires list::lseg<l> * l::GList<a,b,null>
  ensures list::lseg<res> * res::GList<a,b,null>;


HeapPred H1_concat(GList a).
HeapPred H2_concat(GList a).
GList
g_list_concat (GList list1, GList list2)
  infer [H1_concat, H2_concat]
  requires H1_concat(list1)* H2_concat(list2)
  ensures true;
{
  GList tmp_list;

  //  if (list2 !=null)
  //  {
      dprint;
      tmp_list = g_list_last(list1);
      dprint;
      // }

  return list1;
}
