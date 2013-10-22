/*fail:
 g_list_append (last should lseg + case)
 g_list_insert (x)
 g_list_concat
g_list_copy
*/
data GList { int key;
  GList prev;
  GList next;
}

lseg<p> == self=p
  or self::GList<_,_,n> * n::lseg<p> & self!=null;

dlseg<x,y> == self=y & x=null
  or self::GList<_,x,n> * n::dlseg<self,y> & self!=null;

/**
 * g_list_alloc:
 * @Returns: a pointer to the newly-allocated #GList element.
 *
 * Allocates space for one #GList element. It is called by
 * g_list_append(), g_list_prepend(), g_list_insert() and
 * g_list_insert_sorted() and so is rarely used on its own.
 **/
GList g_list_alloc ()
 requires true
  ensures res::GList<_,_,_>;

GList _g_list_alloc ()
 requires true
  ensures res::GList<_,_,_>;

/**
 * g_list_free_1:
 * @list: a #GList element
 *
 * Frees one #GList element.
 * It is usually used after g_list_remove_link().
 */
/**
 * g_list_free1:
 *
 * Another name for g_list_free_1().
 **/
void
 _g_list_free1 (GList list)
requires list::GList<_,_,_>
  ensures true;

/**
 * g_list_append:
 * @list: a pointer to a #GList
 * @data: the data for the new element
 *
 * Adds a new element on to the end of the list.
 *
 * <note><para>
 * The return value is the new start of the list, which 
 * may have changed, so make sure you store the new value.
 * </para></note>
 *
 * <note><para>
 * Note that g_list_append() has to traverse the entire list 
 * to find the end, which is inefficient when adding multiple 
 * elements. A common idiom to avoid the inefficiency is to prepend 
 * the elements and reverse the list when all elements have been added.
 * </para></note>
 *
 * |[
 * /&ast; Notice that these are initialized to the empty list. &ast;/
 * GList *list = NULL, *number_list = NULL;
 *
 * /&ast; This is a list of strings. &ast;/
 * list = g_list_append (list, "first");
 * list = g_list_append (list, "second");
 * 
 * /&ast; This is a list of integers. &ast;/
 * number_list = g_list_append (number_list, GINT_TO_POINTER (27));
 * number_list = g_list_append (number_list, GINT_TO_POINTER (14));
 * ]|
 *
 * Returns: the new start of the #GList
 */

GList g_list_append (GList    list,
	       int	 key)
 case {
  list=null -> ensures res::GList<key, null, null>;
  list!=null -> requires list::lseg<null>
    ensures list::lseg<q>*q::GList<key, _, null>;
}

HeapPred H_app(GList a).
HeapPred G_app(GList a).

GList g_list_append1 (GList    list,
	       int	 key)
  infer [H_app, G_app]
  requires H_app(list)
  ensures G_app(res);
{
  GList new_list;
  GList last;
  
  new_list = _g_list_alloc ();
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

/**
 * g_list_prepend:
 * @list: a pointer to a #GList
 * @data: the data for the new element
 *
 * Adds a new element on to the start of the list.
 *
 * <note><para>
 * The return value is the new start of the list, which 
 * may have changed, so make sure you store the new value.
 * </para></note>
 *
 * |[ 
 * /&ast; Notice that it is initialized to the empty list. &ast;/
 * GList *list = NULL;
 * list = g_list_prepend (list, "last");
 * list = g_list_prepend (list, "first");
 * ]|
 *
 * Returns: the new start of the #GList
 */
GList
g_list_prepend (GList	 list,
		int  key)
  requires list::lseg<p>
  ensures res::GList<key,null,list> * list::lseg<p>;

HeapPred H_ppp(GList a).
HeapPred G_ppp(GList a).

GList
g_list_prepend1 (GList	 list,
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


/**
 * g_list_insert:
 * @list: a pointer to a #GList
 * @data: the data for the new element
 * @position: the position to insert the element. If this is 
 *     negative, or is larger than the number of elements in the 
 *     list, the new element is added on to the end of the list.
 * 
 * Inserts a new element into the list at the given position.
 *
 * Returns: the new start of the #GList
 */
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
  //  if (tmp_list.prev!=null)
  //  tmp_list.prev.next = new_list;
  new_list.next = tmp_list;
  tmp_list.prev = new_list;
  
  if (tmp_list == list)
    return new_list;
  else
    return list;
}

/**
 * g_list_insert_before:
 * @list: a pointer to a #GList
 * @sibling: the list element before which the new element 
 *     is inserted or %NULL to insert at the end of the list
 * @data: the data for the new element
 *
 * Inserts a new element into the list before the given position.
 *
 * Returns: the new start of the #GList
 */
HeapPred H1_insb(GList a).
HeapPred H2_insb(GList a).
HeapPred G_insb(GList a).
GList
g_list_insert_before (GList   list,
		      GList   sibling,
		      int key)
  infer [H1_insb,H2_insb, G_insb]
  requires H1_insb(list)*H2_insb(sibling)
  ensures G_insb(res);
{
  if (list==null)
    {
      list = g_list_alloc ();
      list.key = key;
      // g_return_val_if_fail (sibling == null, list);
      return list;
    }
  else if (sibling!=null)
    {
      GList node;

      node = _g_list_alloc ();
      node.key = key;
      node.prev = sibling.prev;
      node.next = sibling;
      sibling.prev = node;
      if (node.prev != null)
	{
	  node.prev.next = node;
	  return list;
	}
      else
	{
	  //g_return_val_if_fail (sibling == list, node);
	  return node;
	}
    }
  else
    {
      GList last;

      //last = list;
       last = g_list_last (list);
      // while (last->next)
      //	last = last->next;

      last.next = _g_list_alloc ();
      last.next.key = key;
      last.next.prev = last;
      last.next.next = null;

      return list;
    }
}

/**
 * g_list_concat:
 * @list1: a #GList
 * @list2: the #GList to add to the end of the first #GList
 *
 * Adds the second #GList onto the end of the first #GList.
 * Note that the elements of the second #GList are not copied.
 * They are used directly.
 *
 * Returns: the start of the new #GList
 */
HeapPred H1_concat(GList a).
HeapPred H2_concat(GList a).
HeapPred G_concat(GList a).
GList
g_list_concat (GList list1, GList list2)
  infer [H1_concat, H2_concat, G_concat]
  requires H1_concat(list1)* H2_concat(list2)
  ensures G_concat(res);
{
  GList tmp_list;
  
  if (list2 !=null)
    {
      tmp_list = g_list_last (list1);
      //dprint;
      if (tmp_list!=null){
	tmp_list.next = list2;
        dprint;
      }
      else
	list1 = list2;
      //dprint;
       list2.prev = tmp_list;
    }
  
  return list1;
}

/**
 * g_list_remove:
 * @list: a #GList
 * @data: the data of the element to remove
 *
 * Removes an element from a #GList.
 * If two elements contain the same data, only the first is removed.
 * If none of the elements contain the data, the #GList is unchanged.
 *
 * Returns: the new start of the #GList
 */
HeapPred H_remove(GList a).
HeapPred G_remove(GList a).

GList
g_list_remove (GList	     list,
	       int  key)
infer [H_remove, G_remove]
  requires H_remove(list)
  ensures G_remove(res);
{
  GList tmp;
  
  tmp = list;
  if (tmp!=null)
    {
      if (tmp.key != key)
	list = g_list_remove(tmp.next, key);
      else
	{
	  if (tmp.prev !=null)
	    tmp.prev.next = tmp.next;
	  if (tmp.next!=null)
	    tmp.next.prev = tmp.prev;
	  
	  if (list == tmp)
	    list = list.next;
	  
	  _g_list_free1 (tmp);
	  
          // break;
	}
    }
   return list;
}

/**
 * g_list_remove_all:
 * @list: a #GList
 * @data: data to remove
 *
 * Removes all list nodes with data equal to @data. 
 * Returns the new head of the list. Contrast with 
 * g_list_remove() which removes only the first node 
 * matching the given data.
 *
 * Returns: new head of @list
 */
HeapPred H_rema(GList a).
HeapPred G_rema(GList a).

GList
g_list_remove_all (GList	list,
		   int key)
 infer [H_rema, G_rema]
  requires H_rema(list)
  ensures G_rema(res);
{
  GList tmp = list;

  if (tmp!=null)
    {
      if (tmp.key != key)
	list = g_list_remove_all (tmp.next, key);
      else
	{
	  GList next = tmp.next;

           if (tmp.prev != null)
	    tmp.prev.next = next;
	  else
	    list = next;
	  if (next != null)
	    next.prev = tmp.prev;

	  _g_list_free1 (tmp);
	  list = g_list_remove_all(next, key);
	}
    }
  return list;
}

HeapPred H1_rem_link(GList a).
HeapPred H2_rem_link(GList a).
HeapPred G_rem_link(GList a).

//static inline
 GList
_g_list_remove_link (GList list,
		     GList link)
  infer [H1_rem_link,H2_rem_link, G_rem_link]
  requires H1_rem_link(list) * H2_rem_link(link)
  ensures G_rem_link(res);
{
  if (link !=null)
    {
      if (link.prev !=null)
	link.prev.next = link.next;
      if (link.next !=null)
	link.next.prev = link.prev;
      
      if (link == list)
	list = list.next;
      
      link.next = null;
      link.prev = null;
    }
  
  return list;
}

/**
 * g_list_remove_link:
 * @list: a #GList
 * @llink: an element in the #GList
 *
 * Removes an element from a #GList, without freeing the element.
 * The removed element's prev and next links are set to %NULL, so 
 * that it becomes a self-contained list with one element.
 *
 * Returns: the new start of the #GList, without the element
 */

HeapPred H1_rem_link2(GList a).
HeapPred H2_rem_link2(GList a).
HeapPred G_rem_link2(GList a).

GList
g_list_remove_link (GList list,
		    GList llink)
  infer [H1_rem_link2,H2_rem_link2, G_rem_link2]
  requires H1_rem_link2(list) * H2_rem_link2(link)
  ensures G_rem_link2(res);
{
  return _g_list_remove_link (list, llink);
}

/**
 * g_list_delete_link:
 * @list: a #GList
 * @link_: node to delete from @list
 *
 * Removes the node link_ from the list and frees it. 
 * Compare this to g_list_remove_link() which removes the node 
 * without freeing it.
 *
 * Returns: the new head of @list
 */
HeapPred H1_del_link(GList a).
HeapPred H2_del_link(GList a).
HeapPred G_del_link(GList a).

GList
g_list_delete_link (GList list,
		    GList link_)
  infer [H1_del_link,H2_del_link, G_del_link]
  requires H1_del_link(list) * H2_del_link(link_)
  ensures G_del_link(res);
{
  list = _g_list_remove_link (list, link_);
  _g_list_free1 (link_);

  return list;
}


/**
 * g_list_copy:
 * @list: a #GList
 *
 * Copies a #GList.
 *
 * <note><para>
 * Note that this is a "shallow" copy. If the list elements 
 * consist of pointers to data, the pointers are copied but 
 * the actual data is not.
 * </para></note>
 *
 * Returns: a copy of @list
 */

HeapPred H1_copyw(GList a).
HeapPred H2_copyw(GList a).
HeapPred G_copyw(GList a).

GList
  g_list_copyw (GList list, GList last)
  infer [H1_copyw,H2_copyw, G_copyw]
  requires H1_copyw(list) * H2_copyw(last)
  ensures G_copyw(res);
{
   if (list != null)
    {
      GList tmp = _g_list_alloc ();
      last.next = tmp;
      tmp.prev = last;
      last = tmp;
      last.key = list.key;
      last.next = null;
      return g_list_copyw(list.next, last);
    }

  return null;
}


HeapPred H_copy(GList a).
HeapPred G_copy(GList a).

GList
g_list_copy (GList list)
infer [H_copy, G_copy]
  requires H_copy(list)
  ensures G_copy(res);
{
  GList new_list = null;

  if (list != null)
    {
      GList last;

      new_list = _g_list_alloc ();
      new_list.key = list.key;
      new_list.prev = null;
      last = new_list;
      list = list.next;
      //while (list)
      if (list != null)
	{
	  last.next = _g_list_alloc ();
	  last.next.prev = last;
	  last = last.next;
	  last.key = list.key;
	  list = list.next;
	}
      last.next = null;
    }

  return new_list;
}


/**
 * g_list_nth:
 * @list: a #GList
 * @n: the position of the element, counting from 0
 *
 * Gets the element at the given position in a #GList.
 *
 * Returns: the element, or %NULL if the position is off 
 *     the end of the #GList
 */
GList
g_list_nth (GList list,
	    int  n)
 case {
  list=null -> ensures res=null;
  list!=null -> requires list::lseg<null> ensures res::lseg<null> & res!=null;
}

HeapPred H_nth(GList a).
HeapPred G_nth(GList a).

GList
g_list_nth1 (GList list,
	    int  n)
  infer [H_nth, G_nth]
  requires H_nth(list)
  ensures G_nth(res);
{
  if ((n > 0) && list!=null)
    return g_list_nth1(list.next, n-1);
  
  return list;
}

/**
 * g_list_last:
 * @list: a #GList
 *
 * Gets the last element in a #GList.
 *
 * Returns: the last element in the #GList, 
 *     or %NULL if the #GList has no elements
 */

HeapPred H_last(GList a).
HeapPred G_last(GList a).

GList
 g_list_last2 (GList list)
 case { list=null -> ensures res=null;
   list!=null ->
     requires list::lseg<l> * l::GList<a,b,null>
  ensures list::lseg<res> * res::GList<a,b,null>;
}

GList
 g_list_last (GList list)
 case { list=null -> ensures res=null;
   list!=null ->
     requires list::dlseg<p,l> * l::GList<a,x2,null>
     ensures list::dlseg<p,res> * res::GList<a,x2,null>;
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
