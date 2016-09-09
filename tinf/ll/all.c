#include <stdlib.h>
#include <stdio.h>

typedef struct node {
    int val;
    struct node* next;
} node_t;

//Initialize a null-terminating linked list with length n
node_t* init_ll (int n)
{
  node_t* head = NULL;
  node_t* curr;
  
  for (int i = 0; i < n; i++) {
    curr = malloc(sizeof(node_t));
    curr->val = i;
    curr->next = head;
    head = curr;
  }
  return head;
}

node_t* init_cl (int n)
{
  node_t* head;
  node_t* curr = malloc(sizeof(node_t));
  
  curr->val = 0;
  head = curr;
  
  for (int i = 1; i < n; i++) {
    node_t* next_node = malloc(sizeof(node_t));
    next_node->val = i;
    curr->next = next_node;
    curr = next_node;
  }
  
  curr->next = head;
}

void traverse (node_t* head)
{
  node_t* curr = head;
  while (curr != NULL) {
    printf("%d\n", curr->val);
    curr = curr->next ;
  }
}

void search (node_t* head, int i)
{
  node_t* curr = head;
  while (curr->val != i) {
    curr = curr->next;
  }
  //printf ("Found");
}

void safe_search (node_t* head, int i)
{
  node_t* curr = head;
  while (curr != NULL && curr->val != i) {
    curr = curr->next;
  }
}

node_t* new_ll(int n)
{
  if (n==0)
    return NULL;
  node_t* head = malloc(sizeof(node_t));
  head->val = n;
  head->next = new_ll(n-1);
  return head;
}

int length(node_t* xs)
{
  if (xs == NULL)
    return 0;
  return (1 + length(xs->next));
}
/*
node_t* append(node_t* x, node_t* y)
{
  if (x == NULL) 
    return y;
  node_t* s = x;
  while (x->next != NULL)
    x = x->next;
  x->next = y;
  return s;
}
*/

node_t* append(node_t* x, node_t* y)
{
  if (x == NULL)
    return y;
  x->next = append(x->next, y);
  return x;
}

node_t* new_lseg(node_t* p, int n)
{
  if (n==0)
    return p;
  node_t* x = malloc(sizeof(node_t));
  x->val = n;
  x->next = new_lseg(p, n-1);
  return x;
}

node_t* new_cll(int n)
{
  node_t* x = malloc(sizeof(node_t));
  x->val = n;
  x->next = new_lseg(x,n-1);
  return x;
}

void main ()
{
  //node_t* head = new_ll(abs(-15));
  //traverse(head);
  //safe_search(head, 11);
  //search (head, 101 % 10);
  
  //node_t* x = new_ll(10);
  //node_t* y = new_ll(5);
  //node_t* z = append(x, x);
  //traverse(z);
  
  node_t* x = new_cll(0);
  
}



