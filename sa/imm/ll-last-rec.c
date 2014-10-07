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
HeapPred H_last(node a).
HeapPred G_last(node a, node b).
*/
struct node*
 last (struct node* list)
{
  if (list->next != NULL)
    {
      return last (list->next);
    }
  else return list;
}

