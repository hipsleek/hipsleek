struct GSList {
  int val;
  struct GSList * next;
};

/*@
ll<> == self=null
  or self::GSList<_,p>*p::ll<>;
*/

struct GSList*
g_slist_last (struct GSList *list)
/*@
  requires list::ll<>
  ensures res=null or res::GSList<_,null>;//'
*/
{
  if (list)
    {
      while (list->next)
        /*@
          requires list::GSList<_,p>*p::ll<>
          ensures list'::GSList<_,null>;//'
        */
        list = list->next;
    }

  return list;
}

void main()
/*@
  requires true
  ensures true;
 */
{
  return;
}
