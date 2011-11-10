/*
	COMPLETE TREES
*/

data node2 {
	int val;
	node2 left;
	node2 right; 
}
/*
	- complete binary tree: 
		- a binary tree in which every level, except possibly the deepest is completely filled;
		- at depth n, the height of the tree, all nodes are as far left as possible.
*/

/* the view that we used:
 	- n is the height
	- nmin is the "minim height" 
		- is the length of the shortest path to a leaf (the minimum between the heights for the two children) 
		- we used it to make the insertion easier (because in the insertion there are points where we need to
		know if a subtree is perfect or not)
*/

complete<n, nmin, S> == self = null & n = 0 & nmin = 0 & S = {}
	or self::node2<v, l, r> * l::complete<n-1, nmin1, S1> * r::complete<n-2, nmin2, S2> & nmin = min(nmin1, nmin2) + 1 & S = union({v}, S1, S2)
	or self::node2<v, l, r> * l::complete<n-1, nmin1, S1> * r::complete<n-1, nmin2, S2> & nmin = min(nmin1, nmin2) + 1 & S = union({v}, S1, S2)
	inv nmin >= 0 & (n >= nmin);

int maxim(int a, int b) 
	requires true
	ensures (a < b | res = a) & (a >= b | res = b);
{
	if(a >= b)
		return a;
	else
		return b;
}

int minim(int a, int b) 
	requires true
	ensures (a < b | res = b) & (a >= b | res = a);
{
	if(a >= b)
		return b;
	else
		return a;
}

int height(node2 t) 
	requires t::complete<n, nmin, S>
	ensures t::complete<n, nmin, S> & res = n;
{
	if (t != null)
		return maxim(height(t.left), height(t.right)) + 1;
	else return 0;
}

int min_height(node2 t) 
	requires t::complete<n, nmin, S>
	ensures t::complete<n, nmin, S> & res = nmin;
{
	if (t != null)
		return minim(min_height(t.left), min_height(t.right)) + 1;
	else return 0;
}

void insert(ref node2 t, int v)
	requires t::complete<n, nmin, S> & nmin < n // there is still place to insert
	ensures t'::complete<n, nmin1, S1> & (nmin1 = nmin | nmin1 = nmin + 1) & S1 = union(S, {v});  
	requires t::complete<n, nmin, S> & nmin = n // there is no empty place -> we need to increase the height
	ensures t'::complete<n+1, nmin1, S1> & (nmin1 = nmin | nmin1 = nmin + 1) & S1 = union(S, {v});  
{
	node2 aux;
	
	if(t == null) {
		t = new node2(v, null, null);	
		return;	
	}
	else {
		if(min_height(t.left) < height(t.left)) {		// there is still space in the left subtree
			aux = t.left;
			insert(aux, v);
			t.left = aux;
			return;	
		}
	  else {
      if(min_height(t.right) < height(t.right)) {	// there is still space in the right subtree
        aux = t.right;
				insert(aux, v);
				t.right = aux;
				return;	
			}
			else {
				node2 tmp = t.right;
      	if(height(t.left) == height(t.right)) { // tree is full - we must start another level 
					aux = t.left;
					insert(aux, v);
					t.left = aux;
					return;	
				}
				else {
          aux = t.right;    
					insert(aux, v);
          t.right = aux;
					return;	
				}
			}
		}
	}
}

int is_perfect(node2 t) 
	requires t::complete<n, nmin, S>
	//ensures t::complete<n, nmin> & (nmin != n | res = 1) & (nmin = n | res = 0);
	case {
		nmin = n -> ensures t::complete<n, nmin, S> & res = 1;
		nmin != n -> ensures t::complete<n, nmin, S> & res = 0;
	}
{
	if(t == null)
		return 1;
	else {
		if(height(t.left) != height(t.right))
			return 0;
		else {
			if(is_perfect(t.left) == 1)
				return is_perfect(t.right);	
			else 
				return 0;		
			
		}				
	}
}
