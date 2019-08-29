// Self written code
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

void display(){
	struct node* start = NULL;
	int value = 0;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	debug1();
	start = head;
	while(start != NULL){
		debug2();
		value = start->data;
		printf("%d\n", value);
		start = start->next;
	}
	debug3();
	hardskip();
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


// Driver program to test above functions
int main()
{

	push(&head, 5);
	push(&head, 20);
	push(&head, 4);
	push(&head, 3);
	push(&head, 30);

	// printf("Linked List before sorting \n");
	// printList(head);
	printf("Displaying nodes greater than 15\n");
	debug0();
	display();

	// printf("\nLinked List after sorting \n");
	// printList(head);

	return 0;
}

