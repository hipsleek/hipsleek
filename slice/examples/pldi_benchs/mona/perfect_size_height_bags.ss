/*
	PERFECT TREES 
*/

data node2 {
	int val;
	int flag;
	node2 left;
	node2 right; 
}

/* - perfect binary tree: 
	- a binary tree with all leaf nodes at the same depth.
	- all internal nodes have exactly two children.
  - a perfect binary tree has the maximum number of nodes for a given height.
  - a perfect binary tree has 2^(n+1) - 1 nodes where n is the height of a tree.		
*/			

/* Because a perfect tree can have only 1, 3, 7, 15.. nodes, not all of the nodes contain valuable information. 
Some of the nodes are just dummy nodes. To diferentiate between nodes which contain valuable information and dummy 
nodes, each node contains a flag:
	- flag = 0 => dummy node
	- flag = 1 => valuable information
*/ 
 
/* view for a perfect tree */
perfect<n, s, S> == self = null & n = 0 & s = 0 & S = {}
	or self::node2<v, f, l, r> * l::perfect<n-1, s1, S1> * r::perfect<n-1, s2, S2> 
	& s = 1 + s1 + s2 //& s1 = s2
	& (f = 0 | S = union(S1, S2, {v})) & (f = 1 | S = union(S1, S2))
	inv n >= 0 & s >= 0;

/* 
	- inserts a value into t only it finds an empty (dummy) node
	- returns true if it managed to do the insertion, and false otherwise
*/

bool simple_insert(node2 t, int a) 
	requires t::perfect<n, s, S>
	ensures t::perfect<n, s, S1> & ((S1 = union(S, {a}) & res) | (S1 = S & !res));
{
	if (t == null) {
		return false;
	}
	else {
		if (t.flag == 0) {		// it found a dummy node; therefore, it can do the insertion
			t.val = a;
			t.flag = 1;		// sets the flag to 1 because now the info is valuable 
			return true;
		}
		else {
			if(simple_insert(t.left, a))	
				return true;
			else 
				return simple_insert(t.right, a);

		}
	}
}

/*
	- creates a perfect tree of height n
	- all the nodes are dummy nodes
*/	
node2 create(int n) 
	requires true
	ensures res::perfect<n, s, {}>;
{
	if(n == 0)
		return null;
	else {
		return new node2(0, 0, create(n-1), create(n-1)); 
	}
}

int maxim(int a, int b) 
	requires true
	case {
		a > b -> ensures res = a;
		a <= b -> ensures res = b;
	}
{
	if(a >= b)
		return a;
	else
		return b;
}

int height(node2 t) 
	requires t::perfect<n, s, S>
	ensures t::perfect<n, s, S> & res = n;
{
	if (t != null)
		return maxim(height(t.left), height(t.right)) + 1;
	else return 0;
}

/*
	the full insert method
*/
void insert(ref node2 t, int a)
	requires t::perfect<n, s, S>
	ensures t'::perfect<n1, s1, S1> & (n1 = n | n1 = n+1) & S1 = union(S, {a});
{
	bool si = simple_insert(t, a);
	if(si)
		return;
	else {
		int n = height(t);
		node2 new_tree = create(n);
		t = new node2(a, 1, t, new_tree);
		return;
	}

}



