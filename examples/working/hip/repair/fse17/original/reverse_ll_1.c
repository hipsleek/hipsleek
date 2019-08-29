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
struct node* tmp0 = NULL;
struct node* tmp1 = NULL;
struct node* tmp2 = NULL;
int needed1_sdb = 0;

/* Function to push a node */
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

/* Function to reverse the linked list */
void reverse()
{
	struct node* prev = NULL;					//head_ref is not being taken as a local variable, how do we deal as we										// have this head_ref in repair.txt but not in foo.py-var.py
	struct node* current = NULL;
	struct node* nt = NULL;
	//int prt = 0;
 	if(needed1_sdb == needed1_sdb)
 		needed1_sdb = needed1_sdb;
 	if(needed1_sdb != needed1_sdb)
 		return;
 	debug1();				// Get a if node only here
 	current = head;
	while (current != NULL)			// current != NULL
	{
		debug2();
		nt = current->next;
		current->next = prev;
		prev = current;			// prev = current
		current = nt;		// current = nt
					// Maybe change in values maynot allow to access its value
	}
	debug3();
	head = prev;
	debug4();
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

/* Driver program to test above function*/
int main()
{
	/* Start with the empty list */
	push(&head, 20);
	push(&head, 4);
	push(&head, 15); 
	push(&head, 85);	 
	//push(&head, 86);
	//push(&head, 12);
	//push(&head, 32);
	//push(&head, 78);
	//push(&head, 1);
	printList(head); 
	debug0();
	reverse();
	//traverse();					 
	printf("\n Reversed Linked list \n");
	printList(head);
	printf("\n");
	return 0;
	getchar();
}
