//http://quiz.geeksforgeeks.org/circular-linked-list-set-2-traversal/
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
int needed1_sdb = 0;

/* Function to insert a node at the begining of a Circular
linked list */
struct node * newNode(int data){
	struct node *ptr = (struct node *)malloc(sizeof(struct node));
	ptr->next = NULL;
	ptr->data = data;
	return ptr;
}
void push(struct node **head_ref, int data)
{
	struct node *ptr1 = (struct node *)malloc(sizeof(struct node));
	struct node *temp = *head_ref;
	ptr1->data = data;
	ptr1->next = *head_ref;

	/* If linked list is not NULL then set the next of last node */
	if (*head_ref != NULL)
	{
		while (temp->next != *head_ref)
			temp = temp->next;
		temp->next = ptr1;
	}
	else
		ptr1->next = ptr1; /*For the first node */

	*head_ref = ptr1;
}

void push_buggy(struct node* ptr1){

	struct node *temp = NULL;
	struct node* a = NULL;
	if(needed1_sdb == needed1_sdb)
 		needed1_sdb = needed1_sdb;
 	if(needed1_sdb != needed1_sdb)
 		return;
	debug1();
	ptr1->next = head;
	temp = head;
	a = temp->next;
	while (a != head){
		debug2();
		temp = temp->next;
		a = temp->next;
	}
	debug3();
	temp->next = ptr1;
	head = ptr1;
	debug4();
}
/* Function to print nodes in a given Circular linked list */
void printList(struct node *head)
{
	struct node *temp = head;
	if (head != NULL)
	{
		do
		{
			printf("%d ", temp->data);
			temp = temp->next;
		}
		while (temp != head);
	}
}

/* Driver program to test above functions */
int main()
{
	/* Initialize lists as empty */

	/* Created linked list will be 11->2->56->12 */
	push(&head, 12);
	push(&head, 56);
	push(&head, 11);
	struct node* pt = newNode(2);
	debug0();
	push_buggy(pt);

	printf("Contents of Circular Linked List\n ");
	printList(head);

	return 0;
}

