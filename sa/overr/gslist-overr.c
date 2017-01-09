#include "stdhipmem.h"

struct GSList {
  int val;
  struct GSList* next;
};

struct GSList*
_g_slist_alloc (void)
/*@
  requires true
  ensures res::GSList<_,_>;
*/
{
  //return _g_slist_alloc0 ();
  return malloc(sizeof(struct GSList));
}


/*@
HeapPred H_sortr(GSList a,GSList b).
HeapPred G_sortr(GSList a, GSList b, GSList c, GSList d).
*/
struct GSList *
g_slist_sort_real (struct GSList   *list,
                   int     compare_func,
                   int  user_data)
{
  struct GSList *l1, *l2;

  if (!list)
    return NULL;
  if (!list->next)
    return list;

  l1 = list;
  l2 = list->next;

  while ((l2 = l2->next) != NULL)
  /*@
      infer [H_sortr, G_sortr]
      requires H_sortr(l1, l2)
      ensures G_sortr(l1, l2, l1', l2');
    */
    {
      if ((l2 = l2->next) == NULL)
        break;
      l1=l1->next;
    }
  //todo: l1'::GSList<_,_>;
  l2 = l1->next;
  l1->next = NULL;

  return list;
}

