/*  muh/src/dlink.c by fl
 *  Copyright (C) 2002 Lee Hardy <lee@leeh.co.uk>
 *
 *  $Id: dlink.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
 */

#include <stdlib.h>
#include "dlink.h"
#include "common.h"

dlink_node *
dlink_create(void)
{
  dlink_node *m;

  m = (dlink_node *) xmalloc(sizeof(dlink_node));
  m->data = NULL;
  m->next = NULL;
  m->prev = NULL;

  return m;
}

/* XXX - macro? */
void
dlink_free(dlink_node *m)
{
  xfree(m);
}

void
dlink_add(void *data, dlink_node *m, dlink_list *list)
{
  m->data = data;
  m->next = list->head;
  m->prev = NULL;

  if(list->head != NULL)
    list->head->prev = m;
  else if(list->tail == NULL)
    list->tail = m;

  list->head = m;
}

void
dlink_add_tail(void *data, dlink_node *m, dlink_list *list)
{
  m->data = data;
  m->next = NULL;
  m->prev = list->tail;
  
  if(list->head == NULL)
    list->head = m;
  else if(list->tail != NULL)
    list->tail->next = m;

  list->tail = m;
}

void
dlink_delete(dlink_node *m, dlink_list *list)
{
  /* item is at head */
  if(m->prev == NULL)
    list->head = m->next;
  else
    m->prev->next = m->next;

  /* item is at tail */
  if(m->next == NULL)
    list->tail = m->prev;
  else
    m->next->prev = m->prev;
}

dlink_node *
dlink_find(void *data, dlink_list *list)
{
  dlink_node *ptr;

  for(ptr = list->head; ptr; ptr = ptr->next)
  {
    if(ptr->data == data)
      return ptr;
  }

  return NULL;
}

