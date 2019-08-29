/* avl trees */

/* representation of a node in an avl tree */
data node {
	int val;
	int height;
	node left;
	node right;
}

/* view for avl trees */
avl<size, height> == self = null & size = 0 & height = 0 
	or self::node<_, height, p, q> * p::avl<size1, height1> * q::avl<size2, height2> & size = 1+size1+size2 & 
        height2<=height1+1 & height1<=height2+1 & height = max(height1, height2) + 1 
	inv size >= 0 & height >= 0;

int get_max(int a , int b)
	
	requires true 
	ensures res = max(a, b);

{
	if (a >= b)
		return a;
	else
		return b;
}

int height(node x)

	requires x::avl<m, n>
	ensures x::avl<m, n> & res = n;	

{
	if (x == null)
		return 0;
	else
		return x.height;        
}


node node_error() requires true ensures false;

/* function to insert in an avl tree (inline version) */
node insert_inline(node x, int a)

	requires x::avl<m, n> 
	ensures res::avl<m + 1, n1> & n <= n1 <= n+1;

{
	node k1, tmp, k2;
	int h, hl, hr, hlt;

	if (x == null)
		return new node(a, 1, null, null);
	else
	{
		if (a <= x.val)
		{	
			tmp = x.left;
			x.left = insert_inline(tmp, a);
			if ((height(x.left) - height(x.right)) == 2)
			{
				k1 = x.left;
				if (height(k1.left) > height(k1.right))
				{//SRR
					x.left = k1.right;
					h = get_max(height(k1.right), height(x.right));	
					k1.right = x; 
			
					h = h + 1;
					x.height = h;
					h = get_max(height(k1.left), h);
					h = h + 1;
					k1.height = h;
					
					return k1;					
				}
				else
				{//DLR
					if (height(k1.left) == (height(k1.right) - 1))
					{
						k2 = k1.right;
						x.left = k2.right;
						k1.right = k2.left;
						hr = height(k2.left);
						k2.left = k1; 
						hlt = height(k2.right);
						k2.right = x; 
						
						hl = height(k1.left);
						h = get_max(hl, hr);
						h = h + 1;
						k1.height = h;

						hr = height(x.right); 
						h = get_max(hlt, hr);
						h = h + 1;
						x.height = h;

						h = get_max(height(k1), x.height);
						h = h + 1;
						k2.height = h;
				
						return k2; 
					}
					else 
						return node_error();
				}
			}
			else 
				return node_error();
		}
		else	// right branch 
		{
			tmp = x.right;
			x.right = insert_inline(tmp, a);
			if ((height(x.right) - height(x.left)) == 2)
			{
				k1 = x.right;
				if (height(k1.right) > height(k1.left))
				{// SLR
					x.right = k1.left;
					hr = height(k1.left);
					k1.left = x; 

					hl = height(x.left);
					h = get_max(hr, hl);
					h = h + 1;
					x.height = h;
				
					hr = height(k1.right);
					h = get_max(height(x), hr);
					h = h + 1;
					k1.height = h;
				
					return k1;
				}
				else
				{ // DRR 
					if ((height(k1.left) - 1) == height(k1.right))
					{
						k2 = k1.left;
						
						x.right = k2.left;
						k1.left = k2.right;
						hr = height(k2.left);
						k2.left = x;
						hlt = height(k2.right);
						k2.right = k1;

						hl = height(x.left);
						h = get_max(hl, hr);
						h = h + 1;
						x.height = h;

						hr = height(k1.right);
						h = get_max(hlt, hr);	
						h = h + 1;
						k1.height = h;

						h = get_max(height(x), height(k1));
						k2.height = ++h;
					
						return k2;
					}	
					else
						return node_error();
				}				
			}
			else 
				return node_error();
		}
	}
}
