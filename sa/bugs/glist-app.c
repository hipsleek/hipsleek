
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
