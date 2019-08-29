//http://www.geeksforgeeks.org/splay-tree-set-2-insert-delete/
// This code is adopted from http://algs4.cs.princeton.edu/33balanced/SplayBST.java.html
#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

// An AVL tree node
struct node
{
	int key;
	struct node *left, *right;
};
int done = 0;
int needed1_sdb = 0;

/* Helper function that allocates a new node with the given key and
	NULL left and right pointers. */
struct node* newNode(int key)
{
	struct node* node = (struct node*)malloc(sizeof(struct node));
	node->key = key;
	node->left = node->right = NULL;
	return (node);
}

// A utility function to right rotate subtree rooted with y
// See the diagram given above.
struct node *rightRotate(struct node *x)
{
	printf("HELLO SIR right\n");
	struct node *y = x->left;
	x->left = y->right;
	y->right = x;
	return y;
}

struct node *rightRotatebug(struct node *x)
{
	struct node *y = NULL;
	struct node *z = NULL;
	int once = 0, one = 1;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return y;
	debug1();
	y = x->left;
	z = y->right;
	x->left = z;
	y->right = x;
	while (once != one){
		debug2();
		hardskip();
	}
	debug3();
	hardskip();
	debug4();
	return y;
}

// A utility function to left rotate subtree rooted with x
// See the diagram given above.
struct node *leftRotate(struct node *x)
{
	printf("HELLO SIR letf\n");
	struct node *y = x->right;
	x->right = y->left;
	y->left = x;
	return y;
}

// This function brings the key at root if key is present in tree.
// If key is not present, then it brings the last accessed item at
// root. This function modifies the tree and returns the new root
struct node *splay(struct node *root, int key)
{
	// Base cases: root is NULL or key is present at root
	if (root == NULL || root->key == key)
		return root;

	// Key lies in left subtree
	if (root->key > key)
	{
		// Key is not in tree, we are done
		if (root->left == NULL) return root;

		// Zig-Zig (Left Left)
		if (root->left->key > key)
		{
			// First recursively bring the key as root of left-left
			root->left->left = splay(root->left->left, key);

			// Do first rotation for root, second rotation is done after else
			printf("%d\n", done);
			if (done == 0){
			scanf("%d", &done);
			done = 0;
			debug0();
			root = rightRotatebug(root);
			done = 1;
			}
			else 
				root = rightRotate(root);
		}
		else if (root->left->key < key) // Zig-Zag (Left Right)
		{
			// First recursively bring the key as root of left-right
			root->left->right = splay(root->left->right, key);

			// Do first rotation for root->left
			if (root->left->right != NULL)
				root->left = leftRotate(root->left);
		}

		// Do second rotation for root
		return (root->left == NULL)? root: rightRotate(root);
	}
	else // Key lies in right subtree
	{
		// Key is not in tree, we are done
		if (root->right == NULL) return root;

		// Zig-Zag (Right Left)
		if (root->right->key > key)
		{
			// Bring the key as root of right-left
			root->right->left = splay(root->right->left, key);

			// Do first rotation for root->right
			if (root->right->left != NULL)
				root->right = rightRotate(root->right);
		}
		else if (root->right->key < key)// Zag-Zag (Right Right)
		{
			// Bring the key as root of right-right and do first rotation
			root->right->right = splay(root->right->right, key);
			root = leftRotate(root);
		}

		// Do second rotation for root
		return (root->right == NULL)? root: leftRotate(root);
	}
}




// Function to insert a new key k in splay tree with given root
struct node *insert(struct node *root, int k)
{
	// Simple Case: If tree is empty
	if (root == NULL) return newNode(k);

	// Bring the closest leaf node to root
	root = splay(root, k);			//step into

	// If key is already present, then return
	if (root->key == k) return root;

	// Otherwise allocate memory for new node
	struct node *newnode = newNode(k);

	// If root's key is greater, make root as right child
	// of newnode and copy the left child of root to newnode
	if (root->key > k)
	{
		newnode->right = root;
		newnode->left = root->left;
		root->left = NULL;
	}

	// If root's key is smaller, make root as left child
	// of newnode and copy the right child of root to newnode
	else
	{
		newnode->left = root;
		newnode->right = root->right;
		root->right = NULL;
	}

	return newnode; // newnode becomes new root
}





// // Function to insert a new key k in splay tree with given root
// struct node *insert(struct node *root, int k)
// {
// 	struct node *newnode = newNode(k);
// 	struct node *t1 = NULL;
// 	struct node *t2 = NULL;
// 	int t3 = 0,once = 0;
// 	if(needed1_sdb != needed1_sdb)
//  		needed1_sdb = needed1_sdb;
// 	if(needed1_sdb != needed1_sdb)
// 		return newnode;
// 	debug1();
// 	t1 = newnode->left;
// 	t2 = newnode->right;
// 	t3 = root->key;
// 	root = splay(root, k);
// 	once = once;
// 	if (t3 > k)
// 	{
// 		newnode->right = root;
// 	}
// 	if (t3 > k)
// 	{
// 		t1 = root->left;
// 	}
// 	if (t3 > k)
// 	{
// 		newnode->left = t1;
// 	}
// 	if (t3 > k)
// 	{
// 		root->left = NULL;
// 	}
// 	once  = once;
	
// 	if (t3 < k)
// 	{
// 		newnode->left = root;
// 	}
// 	if (t3 < k)
// 	{
// 		t2 = root->right;
// 	}
// 	if (t3 < k)
// 	{
// 		newnode->right = t2;
// 	}
// 	if (t3 < k)
// 	{
// 		root->right = NULL;
// 	}
// 	once = once;
// 	while(once != t3){
// 		debug2();
// 		once = t3;
// 	}
// 	debug3();
// 	once = once;
// 	debug4();
// 	return newnode;
// }

// A utility function to print preorder traversal of the tree.
// The function also prints height of every node
void preOrder(struct node *root)
{
	if (root != NULL)
	{
		printf("%d ", root->key);
		preOrder(root->left);
		preOrder(root->right);
	}
}

/* Drier program to test above function*/
int main()
{
	struct node *root = newNode(100);
	root->left = newNode(50);
	root->right = newNode(200);
	root->left->left = newNode(40);
	root->left->left->left = newNode(30);
	root->left->left->left->left = newNode(20);
	// debug0();
	root = insert(root, 25); //step into
	printf("Preorder traversal of the modified Splay tree is \n");
	preOrder(root);
	return 0;
}

// This function brings the key at root if key is present in tree.
// If key is not present, then it brings the last accessed item at
// root. This function modifies the tree and returns the new root
