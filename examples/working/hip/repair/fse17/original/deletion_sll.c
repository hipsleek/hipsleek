//http://www.geeksforgeeks.org/delete-a-given-node-in-linked-list-under-given-constraints/
// DON'T DELETE HEAD, preconditions set
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

/* structure of a linked list node */
struct node
{
	int data;
	struct node *next;
};
struct node *head = NULL;
int needed1_sdb = 0;

// Will synbad understand arguments to the function
void deleteNode(struct node *n)
{
	struct node *prev = NULL;
	struct node *b = NULL;
	struct node* c = NULL;
	if(needed1_sdb == needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	debug1();
	prev = head;
	c = prev->next;
	while(c != n){  // prev->next != NULL &&  we have escaped this condition
		debug2();
		prev = prev->next;
		c = prev->next;
	}
	debug3();
	if(c == NULL)
		return;
	b = c->next;
	prev->next = b;
	debug4();
}

/* Utility function to insert a node at the begining */
void push(struct node **head_ref, int new_data)
{
	struct node *new_node =
		(struct node *)malloc(sizeof(struct node));
	new_node->data = new_data;
	new_node->next = *head_ref;
	*head_ref = new_node;
}

/* Utility function to print a linked list */
void printList(struct node *head)
{
	while(head!=NULL)
	{
		printf("%d ",head->data);
		head=head->next;
	}
	printf("\n");
}

/* Driver program to test above functions */
int main()
{
	/* Create following linked list
	12->15->10->11->5->6->2->3 */
	push(&head,3);
	push(&head,2);
	push(&head,6);
	push(&head,5);
	push(&head,11);

	printf("Given Linked List: ");
	printList(head);
	debug0();
	deleteNode(head->next->next->next);
	printf("\nModified Linked List: ");
	printList(head);
	return 0;
}

