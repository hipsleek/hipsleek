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

