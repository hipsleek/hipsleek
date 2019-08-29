//http://www.geeksforgeeks.org/swap-nodes-in-a-linked-list-without-swapping-data/
/* This program swaps the nodes of linked list rather
than swapping the field from the nodes.*/
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

/* A linked list node */
struct node
{
	int data;
	struct node *next;
};
struct node *head = NULL;
int needed1_sdb = 0;

/* Function to swap nodes x and y in linked list by
changing links */
// Using many preconditions
void swapNodes(struct node* prevX, struct node* prevY) {
// If x is not head of linked list
struct node* currX = NULL;
struct node* currY = NULL;
struct node* temp = NULL;
struct node* temp2 = NULL;

currX = prevX->next;
currY = prevY->next;

if (prevX != NULL)
	prevX->next = currY;
if (prevX == NULL) 				// Else make y as new head
	head = currY;

// If y is not head of linked list
if (prevY != NULL)
	prevY->next = currX;
if (prevY == NULL) // Else make x as new head
	head = currX;

// Swap next pointers
temp = currY->next;
temp2 = currX->next;
currY->next = temp2;
currX->next = temp;

}

/* Function to add a node at the begining of List */
void push(struct node** head_ref, int new_data)
{
	/* allocate node */
	struct node* new_node =
		(struct node*) malloc(sizeof(struct node));

	/* put in the data */
	new_node->data = new_data;

	/* link the old list off the new node */
	new_node->next = (*head_ref);

	/* move the head to point to the new node */
	(*head_ref) = new_node;
}

/* Function to print nodes in a given linked list */
void printList(struct node *node)
{
	while(node != NULL)
	{
		printf("%d ", node->data);
		node = node->next;
	}
}

/* Druver program to test above function */
int main()
{
	/* The constructed linked list is:
	1->2->3->4->5->6->7 */
	push(&head, 7);
	push(&head, 6);
	push(&head, 5);
	push(&head, 4);
	push(&head, 3);
	push(&head, 2);
	push(&head, 1);

	printf("\n Linked list before calling swapNodes() ");
	printList(head);
	//we are passing the prev pointers of the nodes to be swapped
	debug0();
	swapNodes(head->next, head->next->next);

	printf("\n Linked list after calling swapNodes() ");
	printList(head);

	return 0;
}

