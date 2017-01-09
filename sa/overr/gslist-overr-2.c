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
HeapPred H_ins(GSList a, GSList b).
HeapPred G_ins(GSList a, GSList b, GSList c, GSList d).
*/

struct GSList*
g_slist_insert (struct GSList   *list,
                int  val,
                int      position)
{
  struct GSList *prev_list;
  struct GSList *tmp_list;
  struct GSList *new_list;

  

 while ((position-- > 0) && tmp_list)
   /*@
      infer [H_ins, G_ins]
      requires H_ins(prev_list, tmp_list)
      ensures G_ins(prev_list, tmp_list, prev_list', tmp_list');
   */
    {
      prev_list = tmp_list;
      tmp_list = tmp_list->next;
    }

  // prev_list = g_slist_nth (tmp_list, position);
  if (prev_list)
    {
      new_list->next = prev_list->next;
      prev_list->next = new_list;
    }
  else
    {
      new_list->next = list;
      list = new_list;
    }

  return list;
}
