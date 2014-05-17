
struct llist_node {
  int value;
  struct llist_node *next;
};

struct llist_head {
  struct llist_node *first;
};

struct llist_node *cmpxchg(struct llist_node** first,
                           struct llist_node* old_entry,
                           struct llist_node* next)
/*@
  requires true
  ensures res::llist_node<_,_>;
*/;

struct llist_node *llist_del_first(struct llist_head *head)
{
  struct llist_node *entry, *old_entry, *next;

  entry = head->first;
  if (entry == NULL)
    return NULL;
  for (;;) {
    /* if (entry == NULL) */
    /*   return NULL; */
    old_entry = entry;
    next = entry->next;
    entry = cmpxchg(&head->first, old_entry, next);
    if (entry == old_entry)
      break;
  }

  return entry;
}

struct llist_node *llist_reverse_order(struct llist_node *head)
{
  struct llist_node *new_head = NULL;

  while(head) {
    struct llist_node *tmp = head;
    head = head->next;
    tmp->next = new_head;
    new_head = tmp;
  }

  return new_head;
}
