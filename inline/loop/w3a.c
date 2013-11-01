struct GSList {
  int val;
  struct GSList * next;
};


struct GSList*
g_slist_last (struct GSList *list)
{
  if (list)
    {
      while (list->next)
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
