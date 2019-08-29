//http://www.geeksforgeeks.org/given-a-linked-list-which-is-sorted-how-will-you-insert-in-sorted-way/
/* Program to insert in a sorted list */
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

/* Link list node */
struct node
{
	int data;
	struct node* next;
};
struct node* head = NULL;
int needed1_sdb = 0;

/* function to insert a new_node in a list. Note that this
function expects a pointer to head_ref as this can modify the
head of the input linked list (similar to push())*/
void sortedInsert(struct node* new_node)
{
	struct node* current = NULL;
	struct node* a = NULL;
	int b = 0;
	int c = 0;
	if(needed1_sdb == needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	// we never take a new_node with data less than head->data
	/* Special case for the head end 
	if (*head_ref == NULL || (*head_ref)->data >= new_node->data)
	{
		new_node->next = *head_ref;
		*head_ref = new_node;
	}
	*/
	/* Locate the node before the point of insertion */
	debug1();
	current = head;
	//	This condition will never arise for our input while loop condition : current->next!=NULL
	a = current->next;
	b = a->data;
	c = new_node->data;
	while (b < c){
		debug2();
		current = current->next;
		a = current->next;
		b = a->data;
		c = new_node->data;
	}
		debug3();
	a = current->next;
	new_node->next = a;
	current->next = new_node;
	debug4();
}

/* BELOW FUNCTIONS ARE JUST UTILITY TO TEST sortedInsert */

/* A utility function to create a new node */
struct node *newNode(int new_data)
{
	/* allocate node */
	struct node* new_node =
		(struct node*) malloc(sizeof(struct node));

	/* put in the data */
	new_node->data = new_data;
	new_node->next = NULL;

	return new_node;
}

/* A utility function to insert a node at the beginning of linked list */
void push(struct node** head_ref, int new_data)
{
	/* allocate node */
	struct node* new_node = newNode(new_data);

	/* put in the data */
	new_node->data = new_data;

	/* link the old list off the new node */
	new_node->next = (*head_ref);

	/* move the head to point to the new node */
	(*head_ref) = new_node;
}

/* Function to print linked list */
void printList(struct node *head)
{
	struct node *temp = head;
	while(temp != NULL)
	{
		printf("%d ", temp->data);
		temp = temp->next;
	}
}

/* Drier program to test count function*/
int main()
{
	/* Start with the empty list */

	push(&head, 50);
	push(&head, 10);
	push(&head, 40);
	push(&head, 20);
	push(&head, 30);

	struct node *new_node = newNode(25);
	debug0();
	sortedInsert(new_node);
	/*
	new_node = newNode(10);
	sortedInsert(&head, new_node);
	new_node = newNode(7);
	sortedInsert(&head, new_node);
	new_node = newNode(3);
	sortedInsert(&head, new_node);
	new_node = newNode(1);
	sortedInsert(&head, new_node);
	new_node = newNode(9);
	sortedInsert(&head, new_node);
	*/
	printf("\n Created Linked List\n");
	printList(head);

	return 0;
}

