//http://quiz.geeksforgeeks.org/linked-list-set-2-inserting-a-node/
// A complete working C program to demonstrate all insertion methods
// on Linked List
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

// A linked list node
struct node
{
int data;
struct node *next;
};
struct node* head = NULL;
int needed1_sdb = 0;
/* Given a reference (pointer to pointer) to the head of a list and 
an int, inserts a new node on the front of the list. */
void push(struct node** head_ref, int new_data)
{
	/* 1. allocate node */
	struct node* new_node = (struct node*) malloc(sizeof(struct node));

	/* 2. put in the data */
	new_node->data = new_data;

	/* 3. Make next of new node as head */
	new_node->next = (*head_ref);

	/* 4. move the head to point to the new node */
	(*head_ref) = new_node;
}

/* Given a node prev_node, insert a new node after the given 
prev_node */
void insertAfter(struct node* prev_node, int new_data)
{
	/*1. check if the given prev_node is NULL */
	if (prev_node == NULL)
	{
	printf("the given previous node cannot be NULL");
	return;
	}

	/* 2. allocate new node */
	struct node* new_node =(struct node*) malloc(sizeof(struct node));

	/* 3. put in the data */
	new_node->data = new_data;

	/* 4. Make next of new node as next of prev_node */
	new_node->next = prev_node->next;

	/* 5. move the next of prev_node as new_node */
	prev_node->next = new_node;
}

/* Given a reference (pointer to pointer) to the head
of a list and an int, appends a new node at the end */
struct node* newNode(int data){
	struct node* new_node = (struct node*) malloc(sizeof(struct node));
	new_node->next = NULL;
	new_node->data = data;
	return new_node;
}

void append(struct node* new_node)
{

	struct node* last = NULL; 
	struct node* a = NULL;
	if(needed1_sdb == needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	debug1();
	if (head == NULL)
  	head = new_node;

    if (head == new_node)
     return;

	last = head; 
	a = last->next;
	while(a != NULL){	
		debug2();
		last = last->next;
		a = last->next;
	}
	debug3();
	last->next = new_node;
	debug4();
}

// This function prints contents of linked list starting from head
void printList(struct node *node)
{
while (node != NULL)
{
	printf(" %d ", node->data);
	node = node->next;
}
}

/* Drier program to test above functions*/
int main()
{
/* Start with the empty list */

// Insert 6. So linked list becomes 6->NULL

// Insert 7 at the beginning. So linked list becomes 7->6->NULL
push(&head, 7);

// Insert 1 at the beginning. So linked list becomes 1->7->6->NULL
push(&head, 1);
struct node* new = newNode(6);
debug0(); 
append(new);
// Insert 4 at the end. So linked list becomes 1->7->6->4->NULL
//append(4);

// Insert 8, after 7. So linked list becomes 1->7->8->6->4->NULL
//insertAfter(head->next, 8);

printf("\n Created Linked list is: ");
printList(head);

return 0;
}

