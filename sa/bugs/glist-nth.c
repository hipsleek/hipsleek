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
  HeapPred H_app(GList a).
  HeapPred G_app(GList a).
*/
struct GList*
g_list_append (struct GList* list,
                int key)
/*@
  infer [H_app, G_app]
  requires H_app(list)
  ensures G_app(res);
*/
{
  struct GList* new_list;
  struct GList* last;

  new_list = g_list_alloc();
  new_list->key = key;
  new_list->next = NULL;

  if (list != NULL)
    {
      last = list;

      last = g_list_last(list);
      last->next = new_list;
      new_list->prev = last;
     
      return list;
    }
  else
    {
      new_list->prev = NULL;
      return new_list;
    }
}

/*@
HeapPred H_ppp(GList a).
HeapPred G_ppp(GList a).
*/

struct GList*
g_list_prepend (struct GList* list,
                 int key)
/*@
  infer [H_ppp, G_ppp]
  requires H_ppp(list)
  ensures G_ppp(res);
*/
{
  struct GList* new_list;
  new_list = g_list_alloc();
  new_list->key = key;
  new_list->next = list;

  if (list != NULL)
    {
      new_list->prev = list->prev;
      if (list->prev != NULL)
        list->prev->next = new_list;
      list->prev = new_list;
    }
  else
    new_list->prev = NULL;
  return new_list;
}

/*@
HeapPred H_nth(GList a).
HeapPred G_nth(GList a, GList b).
*/

struct GList*
g_list_nth (struct GList* list,
	     int n)
{
  while (n > 0 && list != NULL)
    /*@
      infer [H_nth, G_nth]
      requires H_nth(list)
      ensures G_nth(list, list');
    */
    {
      list = list->next;
      n = n - 1;
    }

  return list;
}


/*@
HeapPred H_ins(GList a).
HeapPred G_ins(GList a).
*/

struct GList*
g_list_insert (struct GList* list,
	       int key,
	       int position)
/*@
  infer [H_ins, G_ins]
  requires H_ins(list)
  ensures G_ins(res);
*/
{
  struct GList* new_list;
  struct GList* tmp_list;

  if (position < 0)
    return g_list_append (list, key);
  else if (position == 0)
    return g_list_prepend (list, key);

  tmp_list = g_list_nth (list, position);
  if (tmp_list == NULL)
    return g_list_append (list, key);

  new_list = g_list_alloc ();
  new_list->key = key;
  new_list->prev = tmp_list->prev;

  new_list->next = tmp_list;
  tmp_list->prev = new_list;

  if (tmp_list == list)
    return new_list;
  else
    return list;
}
