struct node {
  int key;
  struct node* next;
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
HeapPred H_last(node@I a).
HeapPred G_last(node a, node b).
*/
struct node*
g_list_last1 (struct node* list)
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

