/* avl trees */

/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* function to return the height of an avl tree */
int height(node x)
{
	if (x == null)
		return 0;
	else
		return x.height;
}

/*  function to rotate left */
node rotate_left(node l, node rl, node rr)
{
	node tmp;
	int v = 10, h;
	
	h = l.height + 1;
	tmp = new node(v, h, l, rl);	
	h++;
	
	return new node(v, h, tmp, rr);
}

/* function to rotate right */
node rotate_right(node ll, node lr, node r)
{
	node tmp; 
	int v = 10, h;
	
	h = r.height + 1;
	tmp = new node(v, h, lr, r);
	h++;

	return new node(v, h, ll, tmp);
}

int get_max(int a , int b)
{
	if (a >= b)
		return a;
	else
		return b;
}

/* double left rotation */
node rotate_double_left(node a, node b, node c, node d, int v1, int v2, int v3)
{
	int tmp1, tmp2;
	int h;

	h = get_max(a.height, b.height);
	h++;
	tmp1 = new node(v1, h, a, b);

	h = get_max(c.height, d.height);
	h++;
	tmp2 = new node(v3, h, c, d);

	h = get_max(tmp1.height, tmp2.height);
	h++;
	return new node(v2, h, tmp1, tmp2);
}

/* double right rotation */
node rotate_double_right(node a, node b, node c, node d, int v1, int v2, int v3)
{
	int tmp1, tmp2;
	int h;

	h = get_max(a.height, b.height);
	h++;
	tmp1 = new node(v3, h, a, b);

	h = get_max(c.height, d.height);
	h++;
	tmp2 = new node(v1, h, c, d);

	h = get_max(tmp1.height, tmp2.height);
	h++;
	return new node(v2, h, tmp1, tmp2);

}

/* functions to build avl trees */
node build_avl1(node x, node y)
{
	int v = 0;
	x.height++;

	return new node(v, x.height, x, y);	
}

void build_avl2(node x, node y, node z)
{
	x.left = y;
	x.right = z;
	x.height++;
}

/* function to delete the smallest element in a bst */
int remove_min(ref node x)
{
	int tmp, v;

	if (x.left == null)
	{
		tmp = x.val;
		x = x.right;
		return tmp; 		
	}
	else
	{
		v = remove_min(x.left);
		
		// rebalance 
		if ((x.right.height - x.left.height) == 2)
		{
			if (((x.right.left.height + 1) == x.right.right.height) || (x.right.left.height == x.right.right.height))  // SLR
				x = rotate_left(x.left, x.right.left, x.right.right);   
			else                                                                                                       // DLR
				x = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right); 
		}
		
		return v;
	}
}

/* function to delete a node in a an avl tree */
void delete(ref node x, int a)
{
	if (x != null)
	{
		if (x.val == a) // x must be deleted
		{
			if (x.right == null)
				x = x.left;
			else 
			{
				x.val = remove_min(x.right); 
				
				//rebalance 
				if ((x.left.height - x.right.height) == 2)
				{
					if (((x.left.left.height - 1) == x.left.right.height) || (x.left.left.height == x.left.right.height))
						x = rotate_right(x.left.left, x.left.right, x.right); // SRR
					else 
						x = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right); // DRR
				}
			}
		}
		else 
			if (x.val < a)
			{
				delete(x.right, a);

				//rebalance
				if ((x.left.height - x.right.height) == 2)
				{
					if (((x.left.left.height - 1) == x.left.right.height) || (x.left.left.height == x.left.right.height))
						x = rotate_right(x.left.left, x.left.right, x.right); // SRR
					else 
						x = rotate_double_right(x.left.left, x.left.right.left, x.left.right.right, x.right); // DRR
				}
				
			}
			else 	
			{
				delete(x.left, a);
				
				// rebalance 
				if ((x.right.height - x.left.height) == 2)
				{
					if (((x.right.left.height + 1) == x.right.right.height) || (x.right.left.height == x.right.right.height))  // SLR
						x = rotate_left(x.left, x.right.left, x.right.right);   
					else                                                                                                       // DLR
						x = rotate_double_left(x.left, x.right.left.left, x.right.left.right, x.right.right);
				}

			}
	}
}

/* function to insert a node in an avl tree (using the rotate functions) */
node insert(node x, int a)
{
	if (x == null)
		return new node (a, 1, null, null);
	else 
	{
		if (a <= x.val)
		{
			x.left = insert(x.left, a);
			// check if we need rotation 
			if ((x.left.height - x.right.height) == 2)
			{
				if (x.left.left.height > x.left.right.height)
					return rotate_right(x.left.left, x.left.right, x.right);
				else
				{
					if (x.left.left.height == (x.left.right.height - 1))
						return rotate_double_left(x.left.left, x.left.right.left, x.left.right.right, x.right, 1, 1, 1);
					else
						node_error();
				}
			}
			else
				node_error();
		}
		else
		{
			x.right = insert(x.right, a);
			if ((x.right.height - x.left.height) == 2)
				if (x.right.right.height > x.right.left.height)
					return rotate_left(x.left, x.right.left, x.right.right);
				else
				{
					if ((x.right.left.height - 1) == x.right.right.height)
						return rotate_double_right(x.left, x.right.left.left, x.right.left.right, x.right.right, 1, 1, 1);
					else
						node_error();
				}
			else 
				node_error();
		}
	}
}

/* function to insert in an avl tree (inline version) */
node insert_inline(node x, int a)
{
	node k1;
	int h, hl, hr, hlt;

	if (x == null)
		return new node(a, 1, null, null);
	else
	{
		if (a <= x.val)
		{
			x.left = inline_insert(x.left, a);
			if ((x.left.height - x.right.height) == 2)
			{
				k1 = x.left;
				if (k1.left.height > k1.right.height)
				{//SRR
					x.left = k1.right;
					h = get_max(k1.right.height, x.right.height);	
					k1.right = x; 
			
					h++;
					x.height = h;
					h = get_max(k1.left.height, h);
					h++;
					k1.height = h;
		
					return k1;					
				}
				else
				{//DLR
					if (k1.left.height == (k1.right.height - 1))
					{
						k2 = k1.right;
						x.left = k2.right;
						k1.right = k2.left;
						hr = k2.left.height;
						k2.left = k1; 
						hlt = k2.right.height;
						k2.right = x; 
						
						hl = k1.left.height;
						h = get_max(hl, hr);
						h++;
						k1.height = h;

						hr = x.right.height; 
						h = get_max(hlt, hr);
						h++;
						x.height = h;

						h = get_max(k1.height, x.height);
						h++;
						k2.height = h;
				
						return k2; 
					}
					else 
						node_error();
				}
			}
			else 
				node_error();
		}
		else	// right branch 
		{
			x.right = inline_insert(x.right, a);
			if ((x.right.height - x.left.height) == 2)
			{
				k1 = x.right;
				if (k1.right.height > k1.left.height)
				{// SLR
					x.right = k1.left;
					hr = k1.left.height;
					k1.left = x; 

					hl = x.left.height;
					h = get_max(hr, hl);
					h++;
					x.height = h;
				
					hr = k1.right.height;
					h = get_max(x.height, hr);
					h++;
					k1.height = h;
				
					return k1;
				}
				else
				{ // DRR 
					if ((k1.left.height - 1) == k1.right.height)
					{
						k2 = k1.left;
						
						x.right = k2.left;
						k1.left = k2.right;
						hr = k2.left.height;
						k2.left = x;
						hlt = k2.right.height;
						k2.right = k1;

						hl = x.left.height;
						h = get_max(hl, hr);
						h++;
						x.height = h;

						hr = k1.right.height;
						h = get_max(hlt, hr);	
						h++;
						k1.height = h;

						h = get_max(x.height, k1.height);
						h++;
						k2.height = h;
					
						return k2;
					}	
					else
						node_error();
				}				
			}
			else 
				node_error();
		}
	}
}


