/* Red black trees */
/* Code transformed from C# */ 

/************ DATA DECLARATIONS ************/

/* data type for the information from a node (type object in C#) */
data Object {
	int inf;
}
 
/* data type for a node in a rb tree (corresponds to a class in C#) */
data RedBlackNode {
	/* the static fields were transformed in global constants */
	int ordKey;                // key associated with the node (the IComparable interface replaced by int)
	Object objData;            // data associated with the key
	int intColor;              // color of the node
	RedBlackNode rbnLeft;      // left child
	RedBlackNode rbnRight;     // right child
	RedBlackNode rbnParent;    // parent node
	
}

/* data type for the red black tree (the random object will be replaced by a primitive) */
data RedBlack{
	int intCount;              // number of nodes 
	int intHashCode;           // randomized hash code used as a key
//	String strIdentifier;      // the owner of the tree                       ///////// NOT SUPPORTED YET
	RedBlackNode rbTree;       // the tree 
	RedBlackNode sentinelNode; // used to indicate a leaf node 
	RedBlackNode lastNodeFound;// the node  that was last found
 	
}


/**************** CONSTANTS ******************/

/* constants (static variables in C#) */
enum Color {RED = 0, BLACK = 1} 


/************* FUNCTIONS ****************/
/* these correspond to methods from classes or primitives */


/* PRIMITIVES */
/* primitive to return a random number */
int get_random_int (); 


/* CONSTRUCTORS */
/* constructs a new node with red color */
RedBlackNode RedBlackNode()
{
	Object o = new Object(0);

	return new RedBlackNode(0,o,RED,null,null,null);
}

/* constructs an empty red-black tree */
RedBlack RedBlack()
{
	//String strIdentifier = "";           //some random string 
	int hashCode = get_random_int();
	Object o = new Object(0);
	RedBlackNode sentinelNode = RedBlackNode();
	
	sentinelNode.intColor = BLACK;
	
	return new RedBlack(0,hashCode,sentinelNode,sentinelNode,sentinelNode);
}

/* the second constructor skipped as we dont have string yet */
////////////////////////////
/// Add constructor here ///
///////////////////////////


/* GET-SET FUNCTIONS */
/* key */
int get_key (RedBlackNode t) 
{
	return t.ordKey;
}

void set_key (int value, ref RedBlackNode t) 
{
	t.ordKey = value; 
}

/* data */
Object get_data (RedBlackNode t) 
{
	return t.objData;
}

void set_data (Object value, ref RedBlackNode t) 
{
	t.objData = value; 
}

/* color */
int get_color (RedBlackNode t) 
{
	return t.intColor;
}

void set_color (int value, ref RedBlackNode t) 
{
	t.intColor = value; 
}

/* left */
RedBlackNode get_left (RedBlackNode t) 
{
	return t.rbnLeft;
}

void set_left (RedBlackNode value, ref RedBlackNode t) 
{
	t.rbnLeft = value; 
}

/* right */
RedBlackNode get_right (RedBlackNode t) 
{
	return t.rbnRight;
}

void set_right (RedBlackNode value, ref RedBlackNode t) 
{
	t.rbnRight = value; 
	return t;
}

/* parent */
RedBlackNode get_parent (RedBlackNode t) 
{
	return t.rbnParent;
}

void set_parent (RedBlackNode value, ref RedBlackNode t) 
{
	t.rbnParent = value; 
}


/* OTHER FUNCTIONS */
/* function that compares two int (a, b); returns -1 if a<b, 0 if a=b and 1 if a>b */
int compareTo(int a, int b)
{
	if (a < b) 
		return -1; 
	else if (a == b)
		return 0; 
	     else
		return 1;
}

/* function to insert a node in a red-black tree */
void add(int key, Object data1, ref RedBlack rbTree)
{
	if (key == 0 || data1 == null)
		return;                                          // HERE we will throw an exception  

	int result = 0;
	RedBlackNode node = RedBlackNode();        // create new node 
	RedBlackNode temp = rbTree.rbTree;         // take the rbTree node of the tree                
	
	/* we find the proper place for the new node */
	while (temp != rbTree.sentinelNode)
	{
		node.rbnParent = temp; 
		result = compareTo(key, temp.ordKey);
		if (result == 0) 
			return;                                  // HERE we will throw an exception 
		if (result > 0)
			temp = temp.rbnRight;
		else 
			temp = temp.rbnLeft; 
	}
	
	/* setup node */
	node.ordKey = key;
	node.objData = data1; 
	node.rbnLeft = rbTree.sentinelNode;
	node.rbnRight = rbTree.sentinelNode;

	if (node.rbnParent != null)
	{
		result = compareTo(node.ordKey, node.rbnParent.ordKey);
		if (result > 0) 
			node.rbnParent.rbnRight = node; 
		else 
			node.rbnParent.rbnLeft = node;
	}
	else 
		rbTree.rbTree = node;           // first node added
	
	restoreAfterInsert(node);
	rbTree.lastNodeFound = node; 
	rbTree.intCount += 1;  
}

/* function to restore the red-black property after insert */
void restoreAfterInsert( RedBlackNode x, RedBlack rbTree )
{
	RedBlackNode y; 

	while (x != rbTree.rbTree && x.rbnParent.intColor == RED)
	{
		if (x.rbnParent == x.rbnParent.rbnParent.rbnLeft)
		{
			y = x.rbnParent.rbnParent.Right;
			if (y != null && y.intColor == RED)
			{
				x.rbnParent.intColor = BLACK;
				y.rbnColor = BLACK; 
				x.rbnParent.rbnParent.intColor = RED; 
				x = x.rbnParent.rbnParent;  
			}
			else
			{
				if (x == x.rbnParent.rbnRight)
				{
					x = x.rbnParent;
					rotateLeft(x);
				}
				x.rbnParent.intColor = BLACk;
				x.rbnParent.intColor = RED; 
				rotateRight(x.rbnParent.rbnParent);
			} 
		}
		else
		{
			y = x.rbnParent.rbnParent.rbnLeft;
			if (y != null && y.Color == RED)
			{
				x.rbnParent.intColor = BLACK;
				y.intColor = BLACK;
				x.rbnParent.rbnParent.Color = RED;
				x = x.rbnParent.rbnParent;
			}
			else
			{
				if (x == x.rbnParent.rbnLeft)
				{
					x = x.rbnParent;
					rotateRight(x);
				}
				x.rbnParent.intColor = BLACK;
				x.rbnParent.rbnParent.intColor = RED;
				rotateLeft(x.rbnParent.rbnParent);
			}
		}
	}
	rbTree.rbTree.intColor = BLACK; 
}

void rotateLeft(RedBlackNode x, RedBlack rbTree)
{
	RedBlackNode y = x.rbnRight;
	
	x.rbnRight = y.rbnLeft;
	
	if (y.rbnLeft != rbTree.sentinelNode)
		y.rbnLeft.rbnParent = x; 
	
	if (y != rbTree.sentinelNode)
		y.rbnParent = x.rbnParent;

	if (x.rbnParent != null)
	{
		if (x == x.rbnParent.rbnLeft)
			x.rbnParent.rbnLeft = y;
		else 
			x.rbnParent.rbnRight = y;
	}
	else 
		rbTree.rbTree = y; 
	
	y.rbnLeft = x; 
	if (x != rbTree.sentinelNode)
		x.rbnParent = y; 
}

void rotateRight(RedBlackNode x, RedBlack rbTree)
{
	RedBlackNode y = x.rbnLeft;

	x.rbnLeft = y.rbnRight;
	if (y.rbnRight != rbTree.sentinelNode)
		y.rbnRight.rbnParent = x;
	
	if (y != rbTree.sentinelNode)	
		y.rbParent = x.rbParent;

	if (x.rbParent != null)
	{
		if (x == x.rbnParent.rbnRight)
			x.rbnParent.rbnRight = y;
		else 
			x.rbnParent.rbnLeft = y;
	}
	else 
		rbTree.rbTree = y;

	y.rbnRight = x;
	if (x != rbTree.sentinelNode)
		x.rbnParent = y;	
}

/* get the data associated with the specified key */
Object getData(int key, RedBlack rbTree)
{
	int result;

	RedBlackNode treeNode = rbTree.rbTree;
	
	while (treeNode != rbTree.sentinelNode)
	{
		result = compareTo(key, treeNode.ordKey);
		if (result == 0)
		{
			rbTree.lastNodeFound = treeNode; 
			return treeNode.objData;
		}
		if (result < 0)
			treeNode = treeNode.rbnLeft;
		else
			treeNode = treeNode.rbnRight;		
	}
	// SHOULD THROW AN EXCEPTION HERE
}

/* return the minimum key value */
int getMinKey(RedBlack rbTree)
{
	RedBlackNode treeNode = rbTree.rbTree; 
	
	if (treeNode == null || treeNode == rbTree.sentinelNode)
		return -1;                                      // SHOULD THROW AN EXCEPTION 
	
	while (treeNode.rbnLeft != rbTree.sentinelNode)
		treeNode = treeNode.rbnLeft; 

	rbTree.lastNodeFound = treeNode;
	
	return treeNode.ordKey;
}

/* return the maximum key value */
int getMaxKey (RedBlack tbTree)
{
	RedBlackNode treeNode = rbTree.rbTree;

	if (treeNode == null || treeNode == rbTree.sentinelNode)
		return -1;                                      // SHOULD THROW AN EXCEPTION 

	while (treeNode.rbnRight != rbTree.sentinelNode)
		treeNode = treeNode.rbnRight;	 
	
	rbTree.lastNodeFound = treeNode; 
	
	return treeNode.ordKey;
}

/* returns the object with the minimum key value */
Object getMinValue(redBlack rbTree)
{
	return getData(getMinKey(rbTree), rbTree);
} 

/* returns the object with the minimum key value */
Object getMinValue(redBlack rbTree)
{
	return getData(getMinKey(rbTree), rbTree);
} 

/* is the tree empty? */
bool isEmpty(RedBlack rbTree)
{
	return (rbTree.rbTree == null);
}

/* removes a node from the rb tree */
void remove(int key, RedBlack rbTree)
{
	if (key == 0)                                  // THIS SHOULD HAVE BEEN NULL
		return;                               // THROW AN EXCEPTION 

	int result;
	RedBlackNode node, node1; 

	result = compareTo(key, rbTree.lastNodeFound);
	if (result == 0)
		node = rbTree.lastNodeFound; 
	else 
	{
		node = rbTree.rbTree;
		while (node != rbTree.sentinelNode)
		{
			result = compareTo(key, node.ordKey);
			if (result == 0)
			{
				node1 = node;
				//here should be break, this was added until break will be available
				node = rbTree.sentinelNode;
			}
			if (result < 0)
			{
				node = node.rbnLeft;
				node1 = node;
			}
			else
			{
				node = node.rbnRight;
				node1 = node;				
			}
		}
		node = node1; 
		if (node == rbTree.sentinelNode)
			return;                    // key not found
	}
	
	delete(node);

	rbTree.intCount -= 1;
}

/* deletes a node from the rb tree and restore the rb property */
void delete(RedBlackNode z, RedBlack rbTree)
{
	RedBlackNode x = RedBlackNode(); 
	RedBlackNode y;

	if (z.rbnLeft == rbTree.sentinelNode || z.rbnRight == rbTree.sentinelNode)
		y = z; 
	else
	{
		y = z.rbnRight; 
		while (y.rbnLeft != rbTree.sentinelNode)
			y = y.rbnLeft;
	}
	
	if (y.rbnLeft != rbTree.sentinelNode)
		x = y.rbnLeft; 
	else
		x = y.rbnRight;

	x.rbnParent = y.rbnParent;
	if (y.rbnParent != null)
		if (y == y.rbnParent.rbnLeft)
			y.rbnParent.rbnLeft = x; 
		else 
			y.rbnParent.rbnRight = x;
	else 
		rbTree.rbtree = x; 

	if (y != z)
	{
		z.ordKey = y.ordKey;
		z.objData = y.objData;
	}

	if (y.intColor == BLACK)
		RestoreAfterDelete(x);

	rbTree.lastNodeFound = rbTree.sentinelNode;
}

/* restore the rb properties after delete */
void restoreAfterDelete(RedBlackNode x, redBlack rbTree)
{
	RedBlackNode y;

	while (x != rbTree.rbTree && x.intColor == BLACK)
	{
		if (x == x.rbnParent.rbnLeft)
		{
			y = x.rbnParent.rbnRigt;
			if (y.intColor == RED)
			{
				y.intColor = BLACK; 
				x.rbnParent.intColor = RED;
				RotateLeft(x.rbnParent);
				y = x.rbnParent.rbnRight;
			}
			if (y.rbnLeft.intColor == BLACK && y.rbnRight.intColor == BLACk)
			{
				y.intColor = RED;
				x = x.rbnParent;
			}
			else 
			{
				if (y.rbnRight.intColor == BLACK)
				{
					y.rbnLeft.intColor = BLACK;
					y.intColor = RED;
					rotateRight(y);
					y = x.rbnParent.rbnRight;
				}
				y.intColor = x.rbnParent.intColor; 
				x.rbnParent.intColor = BLACK;
				y.rbnRight.intColor = BLACK;
				rotateLeft(x.rbnParent);
				x = rbTree.rbTree;
			}
		}
		else 
		{
			y = x.rbnParent.rbnLeft;
			if (y.intColor == RED)
			{
				y.intColor = BLACK;
				x.rbnParent.intColor = RED;
				rotateRight(x.rbnParent);
				y = x.rbnparent.rbnLeft;
			}
			if (y.rbnRight.intColor == BLACK && y.rbnLeft.intColor == BLACK)
			{
				y.intColor = RED;
				x = x.rbnParent;
			}
			else
			{
				if (y.rbnLeft.intColor == BLACK)
				{
					y.rbnRight.intColor = BLACK;
					y.intColor = RED;
					rotateLeft(y);
					y = x.rbnParent.rbnLeft;
				}
				y.intColor = x.rbnParent.intColor;
				x.rbnParent.intColor = BLACk;
				y.rbnLeft.intColor = BLACK;
				rotateRight(x.rbnParent);
				x = rbTree.rbTree;
			}
		}
	}
	x.intColor = BLACK;
}

/* function to remove the node with the minimum key */
void removeMin(RedBlack rbTree)
{
	if (rbTree.rbTree == null)
		return;                   // HERE WE SHOULD RTHROW AN EXCEPTION
	
	Remove(getMinKey(rbTree), rbTree);	
}

/* function to remove the node with the maximum key */
void removeMax(RedBlack rbTree)
{
	if (rbTree.rbTree == null)
		return;                   // HERE WE SHOULD RTHROW AN EXCEPTION
	
	Remove(getMaxKey(rbTree), rbTree);	
}

/* empties the tree */
void clear(RedBlack rbTree)
{
	rbTree.rbTree = rbTree.sentinelNode;
	rbTree.intCount = 0;
}

/* returns the size of the tree */
int size(RedBlack rbTree)
{
	return rbTree.intCount;
}
