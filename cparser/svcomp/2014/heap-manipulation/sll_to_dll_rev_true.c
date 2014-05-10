//#include <stdlib.h>

int rand()
/*@
  requires true ensures true;
*/
  ;

extern int __VERIFIER_nondet_int(void);

int __VERIFIER_nondet_int(void) {
    return rand() / 1000;
}

static void fail(void) {
ERROR:
    goto ERROR;
}

#define ___SL_ASSERT(cond) do {     \
    if (!(cond))                    \
        fail();                     \
} while (0)

#ifndef PREDATOR
#   define ___sl_plot(...) do { } while (0)
#endif

struct node {
    struct node *next;
    struct node *prev;
};

struct node * free(struct node* x)
/*@
  requires x::node<_,_>
  ensures res = null;
*/
{
  return NULL;
}

struct node* abort()
/*@
  requires true ensures true & flow __Error;
*/
  ;

struct node* malloc(int n)
/*@
  requires true
  ensures res::node<_,_>;
*/
  ;

static struct node* alloc_node(void)
{
    struct node *ptr = malloc(sizeof *ptr);
    if (!ptr)
        abort();

    ptr->next = NULL;
    ptr->prev = NULL;
    return ptr;
}

static void chain_node(struct node **ppnode)
{
    struct node *node = alloc_node();
    node->next = *ppnode;
    *ppnode = node;
}

static struct node* create_sll(const struct node **pp1, const struct node **pp2)
{
    struct node *list = NULL;

    do
        chain_node(&list);
    while (__VERIFIER_nondet_int());
    /*
    *pp2 = list;

    do
        chain_node(&list);
    while (__VERIFIER_nondet_int());

    *pp1 = list;

    do
        chain_node(&list);
    while (__VERIFIER_nondet_int());
    */
    return list;
}

void init_back_link(struct node *list) {
    for (;;) {
        struct node *next = list->next;
        if (!next)
            return;

        next->prev = list;
        list = next;
    }
}

void reverse_dll(struct node *list) {
    while (list) {
        struct node *next = list->next;
        list->next = list->prev;
        list->prev = next;
        list = next;
    }
}

void remove_fw_link(struct node *list) {
    while (list) {
        struct node *next = list->next;
        list->next = NULL;
        list = next;
    }
}

void check_seq_next(const struct node *beg, const struct node *const end) {
    ___SL_ASSERT(beg);
    ___SL_ASSERT(end);

    for (beg = beg->next; end != beg; beg = beg->next)
        ___SL_ASSERT(beg);
}

void check_seq_prev(const struct node *beg, const struct node *const end) {
    ___SL_ASSERT(beg);
    ___SL_ASSERT(end);

    for (beg = beg->prev; end != beg; beg = beg->prev)
        ___SL_ASSERT(beg);
}

int main()
{
    const struct node *p1, *p2;

    struct node *list = create_sll(&p1, &p2);
    /*
    ___sl_plot(NULL, &list, &p1, &p2);
    check_seq_next(p1, p2);
    ___SL_ASSERT(!p1->prev);
    ___SL_ASSERT(!p2->prev);

    init_back_link(list);
    ___sl_plot(NULL, &list, &p1, &p2);
    check_seq_next(p1, p2);
    check_seq_prev(p2, p1);

    reverse_dll(list);
    ___sl_plot(NULL, &list, &p1, &p2);
    check_seq_prev(p1, p2);
    check_seq_next(p2, p1);

    remove_fw_link(list);
    ___sl_plot(NULL, &list, &p1, &p2);
    check_seq_prev(p1, p2);

    while (list) {
        struct node *prev = list->prev;
        free(list);
        list = prev;
       }*/

    return 0;
}
