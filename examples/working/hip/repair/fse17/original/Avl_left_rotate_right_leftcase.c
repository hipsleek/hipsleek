// http://www.geeksforgeeks.org/avl-tree-set-1-insertion/
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>
#define false 0

// An AVL tree node
struct node
{
	int key;
	struct node *left;
	struct node *right;
	int height;
};
int needed1_sdb = 0;
int done = 0;
struct node *root = NULL;

// A utility function to get maximum of two integers

// A utility function to get height of the tree
int height(struct node *N)
{
	if (N == NULL)
		return 0;
	return N->height;
}

// A utility function to get maximum of two integers
int max(int a, int b)
{
	return (a > b)? a : b;
}

/* Helper function that allocates a new node with the given key and
	NULL left and right pointers. */
struct node* newNode(int key)
{
	struct node* node = (struct node*)
						malloc(sizeof(struct node));
	node->key = key;
	node->left = NULL;
	node->right = NULL;
	node->height = 1; // new node is initially added at leaf
	return(node);
}

// A utility function to right rotate subtree rooted with y
// See the diagram given above.
struct node *rightRotate(struct node *y)
{
	struct node *x = y->left;
	struct node *T2 = x->right;

	// Perform rotation
	x->right = y;
	y->left = T2;

	// Update heights
	y->height = max(height(y->left), height(y->right))+1;
	x->height = max(height(x->left), height(x->right))+1;

	// Return new root
	return x;
}

// A utility function to left rotate subtree rooted with x
// See the diagram given above.
struct node *leftRotate(struct node *x)
{
	struct node *y = NULL;
	struct node *T2 = NULL;

	int m = 0, n = 0;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return y;

	debug1();
	y = x->right;
	T2 = y->left;

	// Perform rotation
	y->left = x;
	x->right = T2;
	// Update heights
	n = max(height(x->left), height(x->right))+1;
	m = max(height(y->left), height(y->right))+1;
	x->height = n;
	y->height = m;

	while(n != m){
		debug2();
		hardskip();
	}
	debug3();
	hardskip();
	debug4();
	// Return new root
	return y;
}

// Get Balance factor of node N
int getBalance(struct node *N)
{
	if (N == NULL)
		return 0;
	return height(N->left) - height(N->right);
}

struct node* insert(struct node* node, int key)
{
	/* 1. Perform the normal BST rotation */
	if (node == NULL)
		return(newNode(key));

	if (key < node->key)
		node->left = insert(node->left, key);
	else
		node->right = insert(node->right, key);		//step here

	/* 2. Update height of this ancestor node */
	node->height = max(height(node->left), height(node->right)) + 1;

	/* 3. Get the balance factor of this ancestor node to check whether
	this node became unbalanced */
	int balance = getBalance(node);

	// If this node becomes unbalanced, then there are 4 cases

	// Left Left Case
	if (balance > 1 && key < node->left->key){
		printf("HELLO GIVE HERE LetfLeft , %d\n" , key);
		scanf("%d", &done);
		return rightRotate(node);
	}

	// Right Right Case
	if (balance < -1 && key > node->right->key){
		printf("HELLO GIVE HERE RightRight , %d\n" , key);
		scanf("%d", &done);
		return leftRotate(node);
	}

	// Left Right Case
	if (balance > 1 && key > node->left->key)
	{
		node->left = leftRotate(node->left);
		printf("HELLO GIVE HERE Letf right , %d\n" , key);
		scanf("%d", &done);
		return rightRotate(node);
	}

	// Right Left Case
	// This is done to call synbad only once on leftRotate
	if (balance < -1 && key < node->right->key && done == 0)
	{
		node->right = rightRotate(node->right);
		done = 1;
		struct node* temp = NULL;
		printf("HELLO GIVE HERE right left, %d \n", key);
		scanf("%d", &done);
		debug0();
		temp = leftRotate(node);
		return temp;
	}

	// Right Left Case
	if (balance < -1 && key < node->right->key && done != 0)
	{
		node->right = rightRotate(node->right);
		printf("HELLO GIVE HERE RightLetf , %d\n" , key);
		scanf("%d", &done);
		return leftRotate(node);
	}

	/* return the (unchanged) node pointer */
	return node;
}

// A utility function to print preorder traversal of the tree.
// The function also prints height of every node
void preOrder(struct node *root)
{
	if(root != NULL)
	{
		printf("%d ", root->key);
		preOrder(root->left);
		preOrder(root->right);
	}
}

/* Drier program to test above function*/
int main()
{
/* Constructing tree given in the above figure */
root = insert(root, 10);
root = insert(root, 25);
root = insert(root, 2);
root = insert(root, 30);
root = insert(root, 28);  //Step here into 
root = insert(root, 50);


/* The constructed AVL Tree would be
		 30
		/ \
	   20  40
		/ \	 \
	   10 25 50
*/

printf("Pre order traversal of the constructed AVL tree is \n");
preOrder(root);
return 0;
}
