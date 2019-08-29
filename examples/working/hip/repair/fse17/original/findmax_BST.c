//http://www.geeksforgeeks.org/print-nodes-at-k-distance-from-root/
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

/* A binary tree node has data, pointer to left child
and a pointer to right child */
struct node
{
int data;
struct node* left;
struct node* right;
};
struct node *root = NULL;
int needed1_sdb = 0;

void printmax()
{
//
	struct node* a = NULL;
	struct node *chk = NULL;
	int b = 0;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	debug1();
	if(root == NULL) 
		return;
	a = root;
	chk = a->right;

	while(chk != NULL){
		debug2();
		a = a->right;
		b = a->data;
		chk = a->right;
	}

	debug3();
	printf("%d\n", b);
	debug4();
}

/* Helper function that allocates a new node with the
given data and NULL left and right pointers. */
struct node* newNode(int data)
{
struct node* node = (struct node*)
					malloc(sizeof(struct node));
node->data = data;
node->left = NULL;
node->right = NULL;

return(node);
}

/* Driver program to test above functions*/
int main()
{

/* Constructed binary tree is
		1
	   /  \
	  2    3
	 / \  /
	4	5 8
*/
root = newNode(1);
root->left	 = newNode(2);
root->right	 = newNode(3);
root->left->left = newNode(4);
root->left->right = newNode(5);
root->right->left = newNode(8); 
debug0();
printmax();

return 0;
}

