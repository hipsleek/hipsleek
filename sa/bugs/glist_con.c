struct GList {
  int key;
  struct GList* prev;
  struct GList* next;
};

/* struct GList* */
/* g_list_last (struct GList* list) */
/* /\*@ */
/* case { */
/*   list=null -> ensures res=null; */
/*   list!=null -> */
/*     requires list::dlseg<l> * l::GList<a,_,null> */
/*     ensures list::dlseg<res> * res::GList<a,_,null>; */
/* } */
/* *\/; */

/*@
HeapPred H_last(GList a).
HeapPred G_last(GList a, GList b).
*/
struct GList*
g_list_last1 (struct GList* list)
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
HeapPred H1_concat(GList a).
HeapPred H2_concat(GList a).
HeapPred G_concat(GList a).
*/
struct GList*
g_list_concat (struct GList* list1,
                struct GList* list2)
/*@
  infer [H1_concat, H2_concat, G_concat]
  requires H1_concat(list1) * H2_concat(list2)
  ensures G_concat(res);
*/
{
  struct GList* tmp_list;

  if (list2 != NULL)
    {
      tmp_list = g_list_last1 (list1);
      if (tmp_list != NULL) {
	tmp_list->next = list2;
      }
      else
	list1 = list2;
      list2->prev = tmp_list;
    }

  return list1;
}
