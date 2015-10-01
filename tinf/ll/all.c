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
  printf ("Found");
}

void safe_search (node_t* head, int i)
{
  node_t* curr = head;
  while (curr != NULL && curr->val != i) {
    curr = curr->next;
  }
}

void main ()
{
  node_t* head = init_cl(10);
  //traverse(head);
  //safe_search(head, 11);
  search (head, 101 % 10);
}



