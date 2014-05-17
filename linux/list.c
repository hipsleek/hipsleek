
struct list_head {
  struct list_head *next;
  struct list_head *prev;
};

void INIT_LIST_HEAD(struct list_head *list)
{
  list->next =list;
  list->prev = list;
}

void __list_add(struct list_head *new,
                struct list_head *prev,
                struct list_head *next)
{
  next->prev = new;
  new->next = next;
  new->prev = prev;
  prev->next = new;
}

void list_add(struct list_head *new,
              struct list_head *head)
{
  __list_add(new, head, head->next);
}

void list_add_tail(struct list_head *new,
                   struct list_head *head)
{
  __list_add(new, head->prev, head);
}

void __list_del(struct list_head *prev,
                struct list_head *next)
{
  next->prev = prev;
  prev->next = next;
}

void __list_del_entry(struct list_head *entry)
{
  __list_del(entry->prev, entry->next);
}

void list_del(struct list_head *entry)
{
  __list_del(entry->prev, entry->next);
  entry->next = NULL; // LIST_POISON1;
  entry->prev = NULL; // LIST_POISON2;
}

void list_replace(struct list_head *old,
                  struct list_head *new)
{
  new->next = old->next;
  new->next->prev = new;
  new->prev = old->prev;
  new->prev->next = new;
}

void list_replace_init(struct list_head *old,
                       struct list_head *new)
{
  list_replace(old, new);
  INIT_LIST_HEAD(old);
}

void list_del_init(struct list_head *entry)
{
  __list_del_entry(entry);
  INIT_LIST_HEAD(entry);
}

// FAIL
void list_move(struct list_head *list,
               struct list_head *head)
{
  __list_del_entry(list);
  list_add(list, head);
}

// FAIL
void list_move_tail(struct list_head *list,
                    struct list_head *head)
{
  __list_del_entry(list);
  list_add_tail(list, head);
}

int list_is_last(const struct list_head *list,
                 const struct list_head *head)
{
  return list->next == head;
}

int list_empty(const struct list_head *head)
{
  return head->next == head;
}

int list_empty_careful(const struct list_head *head)
{
  struct list_head *next = head->next;
  return (next == head) && (next == head->prev);
}

// FAIL
void list_rotate_left(struct list_head *head)
{
  struct list_head *first;

  if(!list_empty(head)) {
    first = head->next;
    list_move_tail(first, head);
  }
}

int list_is_singular(const struct list_head *head)
{
  return !list_empty(head) && (head->next == head->prev);
}

void __list_cut_position(struct list_head *list,
                         struct list_head *head,
                         struct list_head *entry)
{
  struct list_head *new_first = entry->next;
  list->next = head->next;
  list->next->prev = list;
  list->prev = entry;
  entry->next = list;
  head->next = new_first;
  new_first->prev = head;
}

// FAIL
/* void list_cut_position(struct list_head *list, */
/*                        struct list_head *head, */
/*                        struct list_head *entry) */
/* { */
/*   if (list_empty(head)) */
/*     return; */
/*   if (list_is_singular(head) && */
/*       (head->next != entry && head != entry)) */
/*     return; */
/*   if (entry == head) */
/*     INIT_LIST_HEAD(list); */
/*   else */
/*     __list_cut_position(list, head, entry); */
/* } */

void __list_splice(const struct list_head *list,
				 struct list_head *prev,
				 struct list_head *next)
{
  struct list_head *first = list->next;
  struct list_head *last = list->prev;

  first->prev = prev;
  prev->next = first;

  last->next = next;
  next->prev = last;
}

// FAIL
void list_splice(const struct list_head *list,
                 struct list_head *head)
{
  if (!list_empty(list))
    __list_splice(list, head, head->next);
}

// FAIL
void list_splice_tail(struct list_head *list,
                      struct list_head *head)
{
  if (!list_empty(list))
    __list_splice(list, head->prev, head);
}

// FAIL
void list_splice_init(struct list_head *list,
                      struct list_head *head)
{
  if (!list_empty(list)) {
    __list_splice(list, head, head->next);
    INIT_LIST_HEAD(list);
  }
}

// FAIL
void list_splice_tail_init(struct list_head *list,
                           struct list_head *head)
{
  if (!list_empty(list)) {
    __list_splice(list, head->prev, head);
    INIT_LIST_HEAD(list);
  }
}
