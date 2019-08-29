#include <stdio.h>
#include <stdlib.h>
#include <sdb.h>

enum Color {RED, BLACK};

struct Node
{
	int data;
	int color;
	struct Node *left, *right, *parent;
};

struct Node *root = NULL;
int done = 0;
int needed1_sdb = 0;

struct Node* createNode(int data){
	struct Node *new_node = (struct Node *)malloc(sizeof(struct Node));
	new_node->data = data;
	new_node->left = new_node->right = new_node->parent = NULL;
	return new_node;
}

// void rotateLeft(Node *&, Node *&);
// void rotateRight(Node *&, Node *&);
// void fixViolation(Node *&, Node *&);

// // RBTree() { root = NULL; }
// void insert(const int &n);
// void inorder();
// void levelOrder();

// A recursive function to do level order traversal
void inorderHelper(struct Node *root)
{
	if (root == NULL)
		return;

	inorderHelper(root->left);
	printf("%d\n", root->data);
	inorderHelper(root->right);
}

/* A utility function to insert a new node with given key
in BST */
struct Node* BSTInsert(struct Node* root, struct Node *pt)
{
	/* If the tree is empty, return a new node */
	if (root == NULL)
	return pt;

	/* Otherwise, recur down the tree */
	if (pt->data < root->data)
	{
		root->left = BSTInsert(root->left, pt);
		root->left->parent = root;
	}
	else if (pt->data > root->data)
	{
		root->right = BSTInsert(root->right, pt);
		root->right->parent = root;
	}

	/* return the (unchanged) node pointer */
	return root;
}

// // Utility function to do level order traversal
// void levelOrderHelper(struct Node *root)
// {
// 	if (root == NULL)
// 		return;

// 	std::queue<Node *> q;
// 	q.push(root);

// 	while (!q.empty())
// 	{
// 		Node *temp = q.front();
// 		printf("d\n",temp->data);
// 		q.pop();

// 		if (temp->left != NULL)
// 			q.push(temp->left);

// 		if (temp->right != NULL)
// 			q.push(temp->right);
// 	}
// }

void rotateLeft(struct Node *root, struct Node *pt)
{
	printf("rotateLeft\n");
	struct Node *pt_right = pt->right;

	pt->right = pt_right->left;

	if (pt->right != NULL)
		pt->right->parent = pt;

	pt_right->parent = pt->parent;

	if (pt->parent == NULL)
		root = pt_right;

	else if (pt == pt->parent->left)
		pt->parent->left = pt_right;

	else
		pt->parent->right = pt_right;

	pt_right->left = pt;
	pt->parent = pt_right;
}

int tell(struct Node *tm3, struct Node *tm4, struct Node *pt){
	if(tm3 != NULL && pt != tm4)
		return 1;
	else
		return 0;
}

void rotateRightbuggy(struct Node *root, struct Node *pt)
{
	struct Node *pt_left, *tm2 = NULL;
	struct Node *tm3 = NULL;
	struct Node *tm4 = NULL;
	struct Node *tm1 = NULL;
	int cond = 0,once = 0,one = 1;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;

	debug1();
	pt_left = pt -> left;
	tm1 = pt_left -> right;
	tm2 = pt -> left;
	tm3 = pt -> parent;
	tm4 = tm3 ->left;
	
	pt -> left = tm1;

	if (tm2 != NULL)
		tm2 -> parent = pt;

	pt_left -> parent = tm3;

	cond = tell(tm3,tm4,pt);
	
	if (tm3 == NULL){
		root = pt_left;
	}

	if (pt == tm4){
		tm3->left = pt_left;
	}
	tm4 = tm3 -> left;

	if (cond == one){
		tm3 -> right = pt_left;
	}

	pt_left -> right = pt;
	pt -> parent = pt_left;
	while(once != one){
		debug2();
		hardskip();
	}
	debug3();
	hardskip();
	debug4();

}

void rotateRight(struct Node *root, struct Node *pt)
{
	printf("ROTATERight\n");
	struct Node *pt_left = pt->left;

	pt->left = pt_left->right;

	if (pt->left != NULL)
		pt->left->parent = pt;

	pt_left->parent = pt->parent;

	if (pt->parent == NULL)
		root = pt_left;

	else if (pt == pt->parent->left)
		pt->parent->left = pt_left;

	else
		pt->parent->right = pt_left;

	pt_left->right = pt;
	pt->parent = pt_left;
}


// This function fixes violations caused by BST insertion
void fixViolation(struct Node *root, struct Node *pt)
{
	struct Node *parent_pt = NULL;
	struct Node *grand_parent_pt = NULL;

	printf("HELLo\n");
	while ((pt != root) && (pt->color != BLACK) &&
		(pt->parent->color == RED))
	{

		printf("YOU ARE IN\n");
		parent_pt = pt->parent;
		grand_parent_pt = pt->parent->parent;

		/* Case : A
			Parent of pt is left child of Grand-parent of pt */
		if (parent_pt == grand_parent_pt->left)
		{

			struct Node *uncle_pt = grand_parent_pt->right;

			/* Case : 1
			The uncle of pt is also red
			Only Recoloring required */
			if (uncle_pt != NULL && uncle_pt->color == RED)
			{
				grand_parent_pt->color = RED;
				parent_pt->color = BLACK;
				uncle_pt->color = BLACK;
				pt = grand_parent_pt;
			}

			else
			{
				/* Case : 2
				pt is right child of its parent
				Left-rotation required */
				if (pt == parent_pt->right)
				{
					rotateLeft(root, parent_pt);
					pt = parent_pt;
					parent_pt = pt->parent;
				}

				/* Case : 3
				pt is left child of its parent
				Right-rotation required */
				if (done == 0){
					done = 1;
					printf("HURRAY\n");
					debug0();
					rotateRightbuggy(root, grand_parent_pt);
				}
				else{
					rotateRight(root, grand_parent_pt);
				}
				int t = parent_pt->color;
				parent_pt->color = grand_parent_pt->color;
				grand_parent_pt->color = t;
				// swap(parent_pt->color, grand_parent_pt->color);
				pt = parent_pt;
			}
		}

		/* Case : B
		Parent of pt is right child of Grand-parent of pt */
		else
		{
			struct Node *uncle_pt = grand_parent_pt->left;

			/* Case : 1
				The uncle of pt is also red
				Only Recoloring required */
			if ((uncle_pt != NULL) && (uncle_pt->color == RED))
			{
				grand_parent_pt->color = RED;
				parent_pt->color = BLACK;
				uncle_pt->color = BLACK;
				pt = grand_parent_pt;
			}
			else
			{
				/* Case : 2
				pt is left child of its parent
				Right-rotation required */
				if (pt == parent_pt->left)
				{
					if (done == 0){
						done = 1;
						printf("HURRAY\n");
						debug0();
						rotateRightbuggy(root, grand_parent_pt);
					}
					else
					{
						rotateRight(root, grand_parent_pt);
					}
					pt = parent_pt;
					parent_pt = pt->parent;
				}

				/* Case : 3
				pt is right child of its parent
				Left-rotation required */
				rotateLeft(root, grand_parent_pt);
				int t = parent_pt->color;
				parent_pt->color = grand_parent_pt->color;
				grand_parent_pt->color = t;
				// swap(parent_pt->color, grand_parent_pt->color);
				pt = parent_pt;
			}
		}
	}

	printf("Completed\n");
	root->color = BLACK;
}

// Function to insert a new node with given data
void insert(int data)
{
	struct Node *pt =  createNode(data);

	// Do a normal BST insert
	root = BSTInsert(root, pt);

	// fix Red Black Tree violations
	fixViolation(root, pt);
}

// Function to do inorder and level order traversals
// void RBTree::inorder()	 { inorderHelper(root);}
// void RBTree::levelOrder() { levelOrderHelper(root); }

void inorder(){
	inorderHelper(root);
}

// void levelOrder(){
// 	levelOrderHelper(root);
// }


// Driver Code
int main()
{
	
	insert(79);
	insert(61);
	insert(121);
	insert(43);
	insert(37);			//jump
	insert(23);
	insert(168);

	printf("Inoder Traversal of Created Tree\n");
	inorder();

	printf( "\n\nLevel Order Traversal of Created Tree\n");
	// levelOrder();

	return 0;
}
