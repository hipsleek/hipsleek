/* $Id: dlink.h,v 1.2 2009-02-17 08:55:22 chinwn Exp $ */
#ifndef _DLINK_H_
#define _DLINK_H_

typedef struct _dlink_node dlink_node;
typedef struct _dlink_list dlink_list;

struct _dlink_node
{
    void *data;
    dlink_node *next;
    dlink_node *prev;
};

struct _dlink_list
{
    dlink_node *head;
    dlink_node *tail;
};

dlink_node *dlink_create(void);
void dlink_free(dlink_node *m);

void dlink_add(void *data, dlink_node *m, dlink_list *list);
void dlink_add_tail(void *data, dlink_node *m, dlink_list *list);
void dlink_delete(dlink_node *m, dlink_list *list);
dlink_node *dlink_find(void *data, dlink_list *list);

#endif

