/*
	COMPLETE TREES
*/

data node2[b] {
	b val;
	node2[b] left;
	node2[b] right; 
}
/*
	- complete binary tree: 
		- a binary tree in which every level, except possibly the deepest is completely filled;
		- at depth n, the height of the tree, all nodes are as far left as possible.
*/


ho_pred tree_shape[t,b]<a:t>[Base,Rec,Inv]== Base(a,self)
	or self::node2[n]<v,l,r>* l::tree_shape<al>*m::tree2_3<am> * r::tree_shape<ar>* Rec1(a,al,ar,self,v,l,r)
	inv Inv(a,self);

ho_pred tree_B[t,b]<a:t>[Base,Rec,Inv] refines tree_shape[t,b]<a>
  with { Base(a,self) = self=null}  
  
ho_pred tree_Hmin [int,b]<nmin:int>[Base,Rec,Inv] extends tree_B[int,b]<nmin>
 with 
  { Base (nmin,self) = nmin=0
    Rec (nmin,nminl,nminr,self,v,l,r) = nmin= min(nminl,nminr)+1
    Inv (nmin,self)= nmin>=0
  }
  
ho_pred tree_H [int,b]<n:int>[Base,Rec,Inv] extends tree_B[int,b]<n>
 with 
  { Base(n,self) = n=0
    Rec (n,nl,nr,self,v,l,r) =  nl=n-1 & (nr=n-2 | nr = n-1)
  }
  
ho_pred tree_inv[int,int,b]<nmin,n>[Base,Rec,Inv] refines (tree_H[int,b]<n> combine tree_Hmin[int,b]<nmin>)
  with 
    {Inv(nmin,n,self) = n>=nmin}
  
complete<n, nmin> == finalizes tree_inv[int]<nmin,n>;

/* possible view for a complete tree */
/*
complete<n, nmin> == self = null & n = 0 & nmin = 0
	or self::node2<_, l, r> * l::complete<n-1, nmin1> * r::complete<n-2, nmin2> & nmin = min(nmin1, nmin2) + 1
	or self::node2<_, l, r> * l::complete<n-1, nmin1> * r::complete<n-1, nmin2> & nmin = min(nmin1, nmin2) + 1
	inv nmin >= 0 & n >= nmin;
*/
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
	requires t::complete<n, nmin>
	ensures t::complete<n, nmin> & res = n;
{
	if (t != null)
		return maxim(height(t.left), height(t.right)) + 1;
	else return 0;
}

int min_height(node2 t) 
	requires t::complete<n, nmin>
	ensures t::complete<n, nmin> & res = nmin;
{
	if (t != null)
		return minim(min_height(t.left), min_height(t.right)) + 1;
	else return 0;
}

void insert(ref node2 t, int v)
	requires t::complete<n, nmin> & nmin < n // there is still place to insert
	ensures t'::complete<n, nmin1> & (nmin1 = nmin | nmin1 = nmin + 1);  
	requires t::complete<n, nmin> & nmin = n // there is no empty place -> we need to increase the height
	ensures t'::complete<n+1, nmin1> & (nmin1 = nmin | nmin1 = nmin + 1);  
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
					//assert t'::complete<n1, n1>;
					aux = t.left;
					insert(aux, v);
					t.left = aux;
					return;	
				}
				else {
					aux = t.right;
					//assert aux'::complete<n2, nmin2> & nmin2 = n2;
					insert(aux, v);
					t.right = aux;
					return;	
				}
			}
		}
	}
}

/*int is_perfect(node2 t) 
	requires t::complete<n, nmin>
	ensures t::complete<n, nmin> & (nmin != n | res = 1) & (nmin = n | res = 0);
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
}*/
