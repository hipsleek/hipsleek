// Iterative C program to find length or count of nodes in a linked list
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

/* Given a reference (pointer to pointer) to the head
of a list and an int, push a new node on the front
of the list. */
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

/* Counts no. of nodes in linked list */
void getCount() {
	struct node* current = NULL;
	int count = 0,a=0;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	debug1();
	current = head;
	while (current != NULL)
	{
		debug2();
		count = count + 1;
		a = current->data;
		current = current->next;
		printf("%d\n", a);
	}
	debug3();
	printf("%d\n", count);
	debug4();
}

/* Drier program to test count function*/
int main()
{
	/* Start with the empty list */
	/* Use push() to construct below list
	1->2->1->3->1 */
	push(&head, 1);
	push(&head, 3);
	push(&head, 1);
	push(&head, 2);
	push(&head, 1);

	/* Check the count function */
	debug0();
	getCount();
	return 0;
}
