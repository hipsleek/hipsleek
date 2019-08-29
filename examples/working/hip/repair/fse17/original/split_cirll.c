//http://www.geeksforgeeks.org/split-a-circular-linked-list-into-two-halves/
/* Program to split a circular linked list into two halves */
#include <stdio.h> 
#include <stdlib.h> 
#include <sdb.h>

/* structure for a node */
struct node
{
int data;
struct node *next;
}; 
struct node *head = NULL;
struct node *head1 = NULL;
struct node *head2 = NULL; 
int needed1_sdb = 0;

/* Function to split a list (starting with head) into two lists.
head1_ref and head2_ref are references to head nodes of 
	the two resultant linked lists */
void splitList()
{
	struct node *slow_ptr = NULL;
	struct node *fast_ptr = NULL; 
	struct node *a = NULL, *b = NULL, *c = NULL;
	if(needed1_sdb != needed1_sdb)
	 	needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	// we are sending even number of nodes and head!= NULL, so its cool
	debug1();
	/* If there are odd nodes in the circular list then
		fast_ptr->next becomes head and for even nodes 
		fast_ptr->next->next becomes head */
	fast_ptr = head; 
	slow_ptr = head;
	a = fast_ptr->next;
	b = a->next;				// b == fast_ptr->next->next
	// we will never need loop condition : fast_ptr->next != head &&
	while(b != head)
	{
		debug2();
		fast_ptr = b;
		slow_ptr = slow_ptr->next;
		a = fast_ptr->next;
		b = a->next;
	}
	debug3();
	/* If there are even elements in list then move fast_ptr */
	if(b == head)
		fast_ptr = fast_ptr->next;

	/* Set the head pointer of first half */
	head1 = head;

	/* Set the head pointer of second half */
	c = head->next;
	if(c != head)
		head2 = slow_ptr->next;

	/* Make second half circular */
	a = slow_ptr->next;

	/* Make first half circular */
	slow_ptr->next = head;	 
	debug4();
}

/* UTILITY FUNCTIONS */
/* Function to insert a node at the begining of a Circular 
linked lsit */
void push(struct node **head_ref, int data)
{
	struct node *ptr1 = (struct node *)malloc(sizeof(struct node));
	struct node *temp = *head_ref; 
	ptr1->data = data; 
	ptr1->next = *head_ref; 

	/* If linked list is not NULL then set the next of 
		last node */
	if(*head_ref != NULL)
	{
		while(temp->next != *head_ref)
		temp = temp->next;	 
		temp->next = ptr1; 
	}
	else
		ptr1->next = ptr1; /*For the first node */

	*head_ref = ptr1;	 
} 

/* Function to print nodes in a given Circular linked list */
void printList(struct node *head)
{
	struct node *temp = head; 
	if(head != NULL)
	{
		printf("\n");
		do {
		printf("%d ", temp->data);
		temp = temp->next;
		} while(temp != head);
	}
}

/* Driver program to test above functions */
int main()
{
int list_size, i; 

/* Initialize lists as empty */
/* Created linked list will be 12->56->2->11 */
push(&head, 12); 
push(&head, 56); 
push(&head, 2); 
push(&head, 11); 

printf("Original Circular Linked List");
printList(head);	 

/* Split the list */
debug0();
splitList();

printf("\nFirst Circular Linked List");
printList(head1); 

printf("\nSecond Circular Linked List");
// printList(head2); 

// getchar();
return 0;
} 
