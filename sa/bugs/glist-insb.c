
struct GList {
  int key;
  struct GList* prev;
  struct GList* next;
};

struct GList*
g_list_alloc()
/*@
  requires true
  ensures res::GList<_,_,_>;
*/;

/*@
HeapPred H_last(GList a).
HeapPred G_last(GList a, GList b).
*/
struct GList*
g_list_last (struct GList* list)
{
  if (list != NULL) {
    while (list->next != NULL)
    /*@
      infer[H_last, G_last]
      requires H_last(list)
      ensures G_last(list, list');
    */
    {
      list = list->next;
    }
  }

  return list;
}

/*@
HeapPred H1_insb(GList a).
HeapPred H2_insb(GList a).
HeapPred G_insb(GList a).
*/

struct GList*
g_list_insert_before (struct GList* list,
		       struct GList* sibling,
		       int key)
/*@
  infer [H1_insb, H2_insb, G_insb]
  requires H1_insb(list) * H2_insb(sibling)
  ensures G_insb(res);
*/
{
  if (list == NULL)
    {
      list = g_list_alloc ();
      list->key = key;
      return list;
    }
  else if (sibling != NULL)
    {
      struct GList* node;

      node = g_list_alloc ();
      node->key = key;
      node->prev = sibling->prev;
      node->next = sibling;

      sibling->prev = node;
      if (node->prev != NULL)
	{
	  node->prev->next = node;
	  return list;
	}
      else
	{
	  return node;
	}
    }
  else
    {
      struct GList* last;

      last = g_list_last (list);

      last->next = g_list_alloc ();
      last->next->key = key;
      last->next->prev = last;
      last->next->next = NULL;

      return list;
    }
}
