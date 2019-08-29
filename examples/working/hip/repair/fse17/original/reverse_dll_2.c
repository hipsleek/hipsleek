//http://www.geeksforgeeks.org/reverse-a-doubly-linked-list/
/* Program to reverse a doubly linked list */
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

/* a node of the doubly linked list */
struct node
{
int data;
struct node *next;
struct node *prev;
};
struct node* head = NULL;
int needed1_sdb = 0;

/* Function to reverse a Doubly Linked List */
void reverse()
{
	struct node *temp = NULL;
	struct node *current = NULL;
	struct node *temp2 = NULL;
	current = head;
	while (current != NULL)			// temp2 != NULL
	{
	temp = current->prev;
	temp2 = current->next; 			//current->prev;    - copy paste error
	current->prev = temp2;
	current->next = temp;
	current = current->prev;
	}
	debug3();
	if(temp != NULL )
		head = temp->prev;				//removed   did not reset the head
	debug4();
}



/* UTILITY FUNCTIONS */
/* Function to insert a node at the beginging of the Doubly Linked List */
void push(struct node** head_ref, int new_data)
{
	/* allocate node */
	struct node* new_node =
			(struct node*) malloc(sizeof(struct node));

	/* put in the data */
	new_node->data = new_data;				// remove

	/* since we are adding at the begining
	prev is always NULL */
	new_node->prev = NULL;

	/* link the old list off the new node */
	new_node->next = (*head_ref); 					// remove

	/* change prev of head node to new node */
	if((*head_ref) != NULL)
	(*head_ref)->prev = new_node ; 

	/* move the head to point to the new node */
	(*head_ref) = new_node;								
}

/* Function to print nodes in a given doubly linked list 
This function is same as printList() of singly linked lsit */
void printList(struct node *node)
{
while(node!=NULL)
{
printf("%d ", node->data);
node = node->next;
}
} 

/* Drier program to test above functions*/
int main()
{
/* Start with the empty list */

/* Let us create a sorted linked list to test the functions
Created linked list will be 10->8->4->2 */
push(&head, 2);
push(&head, 4);
push(&head, 8);
push(&head, 10);

printf("\n Original Linked list ");
printList(head);

/* Reverse doubly linked list */
debug0();
reverse();

printf("\n Reversed Linked list ");
printList(head);		 

getchar();
}

