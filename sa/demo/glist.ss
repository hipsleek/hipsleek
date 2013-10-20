/*fail:
 g_list_append (last should lseg + case)
 g_list_insert

*/
data GList { int key;
  GList prev;
  GList next;
}

lseg<p> == self=p
  or self::GList<_,_,q> * p::lseg<q> & self!=null;

GList g_list_alloc ()
 requires true
  ensures res::GList<_,_,_>;

HeapPred H_app(GList a).
HeapPred G_app(GList a).

GList g_list_append (GList    list,
	       int	 key)
  infer [H_app, G_app]
  requires H_app(list)
  ensures G_app(res);
{
  GList new_list;
  GList last;
  
  new_list = g_list_alloc ();
  new_list.key = key;
  new_list.next = null;
  
  if (list !=null)
    {
      last = g_list_last (list);
      // g_assert (last != NULL);
      // dprint;
      last.next = new_list;
      new_list.prev = last;

      return list;
    }
  else
    {
      new_list.prev = null;
      return new_list;
    }
}

HeapPred H_ppp(GList a).
HeapPred G_ppp(GList a).

GList
g_list_prepend (GList	 list,
		int  key)
infer [H_ppp, G_ppp]
  requires H_ppp(list)
  ensures G_ppp(res);
{
  GList new_list;
  
  new_list = g_list_alloc ();
  new_list.key = key;
  new_list.next = list;
  
  if (list !=null)
    {
      new_list.prev = list.prev;
      if (list.prev != null)
	list.prev.next = new_list;
      list.prev = new_list;
    }
  else
    new_list.prev = null;
  
  return new_list;
}

HeapPred H_ins(GList a).
HeapPred G_ins(GList a).

GList
g_list_insert (GList	list,
	       int	 key,
	       int	 position)
infer [H_ins, G_ins]
  requires H_ins(list)
  ensures G_ins(res);
{
  GList new_list;
  GList tmp_list;
  
  if (position < 0)
    return g_list_append (list, key);
  else if (position == 0)
    return g_list_prepend (list, key);
  
  tmp_list = g_list_nth (list, position);
  if (tmp_list == null)
    return g_list_append (list, key);
  
  new_list = g_list_alloc ();
  new_list.key = key;
  new_list.prev = tmp_list.prev;
  if (tmp_list.prev!=null)
    tmp_list.prev.next = new_list;
  new_list.next = tmp_list;
  tmp_list.prev = new_list;
  
  if (tmp_list == list)
    return new_list;
  else
    return list;
}

HeapPred H_nth(GList a).
HeapPred G_nth(GList a).

GList
g_list_nth (GList list,
	    int  n)
  infer [H_nth, G_nth]
  requires H_nth(list)
  ensures G_nth(res);
{
  if ((n > 0) && list!=null)
    return g_list_nth(list.next, n-1);
  
  return list;
}

HeapPred H_last(GList a).
HeapPred G_last(GList a).

GList
 g_list_last (GList list)
 case { list=null -> ensures res=null;
   list!=null ->
     requires list::lseg<l> * l::GList<a,b,null>
  ensures list::lseg<res> * res::GList<a,b,null>;
}

GList
 g_list_last1 (GList list)

  infer [H_last, G_last]
  requires H_last(list)
  ensures G_last(res);
{
  if (list != null)
    {
      if (list.next!=null)
	return g_list_last1 (list.next);
    }
  
  return list;
}
