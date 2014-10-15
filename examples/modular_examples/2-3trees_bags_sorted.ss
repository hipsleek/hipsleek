/* 2-3 trees */
data node3 {
	int maxl;	// max left
	int maxm;	// max middle	
	node3 left;
	node3 middle;
	node3 right;
}

tree2_3<h, S> == 
	self = null & h = 0 & S = {} or 
	self::node3<ml, mm, l, m, r> * l::tree2_3<hl, Sl> * m::tree2_3<hm, Sm> * r::tree2_3<hr, Sr> 
		& r != null & hl = hm & hl = hr & h = hl + 1 & S=union(Sl, Sm, Sr, {ml, mm}) or
	self::node3<ml, _, l, m, r> * l::tree2_3<hl, Sl> * m::tree2_3<hm, Sm> 
		& r = null & hl = hm & h = hl + 1 & S=union(Sl, Sm, {ml})
	inv h >= 0;

node3 insert_left(ref node3 x, int a, int type)
	requires x::tree2_3<n, S> & n > 1
	ensures	res::tree2_3<n+1, S1> & x' = null & n > 1 & S1 = union(S, {a}) or
	        x'::tree2_3<n, S> & x = x' & res = null & n > 1;
	requires x::node3<_, _, l, m, r> * l::tree2_3<n1, Sl> * m::tree2_3<n1, Sm> & n1 > 0 & r = null 
	ensures x'::tree2_3<n1+1, S> & x = x' & res = null & n1>0;
{
	node3 tmp1, tmp2;
	if (type == 1)
		tmp1 = x.left;
	else
		tmp1 = x.middle;
	if(tmp1.left != null && tmp1.right == null) {		
		insert(tmp1, a);
		//dprint;
		return null;
	}
	else {	
		if (a < tmp1.maxl) {				// insert in the left subtree
			tmp2 = insert(tmp1.left, a);
			if(tmp2 != null) {
				tmp1.left = tmp1.middle;
				tmp1.middle = tmp1.right;
				tmp1.right = null;
			}
			else {
				if (a < tmp1.maxm) {		// insert in the middle subtree
					tmp2 = insert(tmp1.middle, a);
					if(tmp2 != null) {
						tmp1.middle = tmp1.right;
						tmp1.right = null;
					}
				}
				else {				// insert in the right subtree
					tmp2 = insert(tmp1.right, a);
					if (tmp2 != null) {
						tmp1.right = null;	
					}
				}
			}
		}
		if (tmp2 != null) {
		if(type == 1) {
			if(x.right == null) {			// x has 2 children		
				x.right = x.middle;
				x.middle = x.left;
				x.left = tmp2;
				return null;
			}
			else {					// x has 3 children
				node3 newnode; 
				newnode = new node3(0, 0, tmp2, x.left, null);
				x.left = x.middle;
				x.middle = x.right;
				x.right = null;
				node3 aux = new node3(0, 0, newnode, x, null);
				x = null;
				return aux;
			}
		}
		else {
			if(x.right == null) {			// x has 2 children		
				x.right = x.middle;
				x.middle = tmp2;
				return null;
			}
			else {					// x has 3 children
				node3 newnode = new node3(0, 0, x.left, tmp2, null);
				x.left = x.middle;
				x.middle = x.right;
				x.right = null;
				node3 aux = new node3(0, 0, newnode, x, null);
				x = null;
				return aux;
			}
		}
		}
		else return null;
	}
}


node3 insert_middle(ref node3 x, int a)
	requires x::tree2_3<n, S> & n > 1
	ensures	res::tree2_3<n+1, S1> & x' = null & n > 1 & S1=union(S, {a}) or
		    x'::tree2_3<n, S> & x = x' & res = null & n > 1;
	requires x::node3<_, _, l, m, r> * l::tree2_3<n1, Sl> * m::tree2_3<n1, Sm> & n1 > 0 & r = null 
	ensures x'::tree2_3<n1+1, S> & x = x' & res = null & n1>0;
{

	node3 tmp1, tmp2;
	tmp1 = x.middle;
	if(tmp1.left != null && tmp1.right == null) {
		insert(tmp1, a);
		return null;
	}
	else {	
		if (a < tmp1.maxl) {				// insert in the left subtree
			tmp2 = insert(tmp1.left, a);
			if(tmp2 != null) {
				tmp1.left = tmp1.middle;
				tmp1.middle = tmp1.right;
				tmp1.right = null;
			}
			else {
				if (a < tmp1.maxm) {		// insert in the middle subtree
					tmp2 = insert(tmp1.middle, a);
					if(tmp2 != null) {
						tmp1.middle = tmp1.right;
						tmp1.right = null;
					}
				}
				else {				// insert in the right subtree
					tmp2 = insert(tmp1.right, a);
					if (tmp2 != null) {
						tmp1.right = null;	
					}
				}
			}
		}
		if (tmp2 != null) {
			if(x.right == null) {			// x has 2 children		
				x.right = x.middle;
				x.middle = tmp2;
				return null;
			}
			else {					// x has 3 children
				node3 newnode = new node3(0, 0, x.left, tmp2, null);
				x.left = x.middle;
				x.middle = x.right;
				x.right = null;
				node3 aux = new node3(0, 0, newnode, x, null);
				x = null;
				return aux;
			}
		}
		else return null;
	}
}

node3 insert_right(ref node3 x, int a)
	requires x::node3<_, _, l, m, r> * l::tree2_3<n1, Sl> * m::tree2_3<n1, Sm> * r::tree2_3<n1, Sr>  & n1 > 0
	ensures	res::tree2_3<n1+2, S> & x' = null & n1 > 0 & S=union(Sl, Sm, Sr, {a}) or
		    x'::tree2_3<n1+1, S> & x = x' & res = null & n1 > 0;
{

	node3 tmp1, tmp2;
	tmp1 = x.right;
	if(tmp1.left != null && tmp1.right == null) {
		insert(tmp1, a);
		return null;
	}
	else {	
		if (a < tmp1.maxl) {				// insert in the left subtree
			tmp2 = insert(tmp1.left, a);
			if(tmp2 != null) {
				tmp1.left = tmp1.middle;
				tmp1.middle = tmp1.right;
				tmp1.right = null;
			}
			else {
				if (a < tmp1.maxm) {		// insert in the middle subtree
					tmp2 = insert(tmp1.middle, a);
					if(tmp2 != null) {
						tmp1.middle = tmp1.right;
						tmp1.right = null;
					}
				}
				else {				// insert in the right subtree
					tmp2 = insert(tmp1.right, a);
					if (tmp2 != null) {
						tmp1.right = null;	
					}
				}
			}
		}
		if (tmp2 != null) {
			// x has 3 children
			node3 newnode = new node3(0, 0, x.right, tmp2, null);
			x.right = null;
			node3 aux = new node3(0, 0, x, newnode, null);
			x = null;
			return aux;
		}
		else return null;
	}
}

node3 insert(ref node3 x, int a)
	requires x::tree2_3<n, S> 
	ensures res::tree2_3<n+1, S1> & x' = null & S1=union(S, {a}) or
	        x'::tree2_3<n, S> & x = x' & res = null & x' != null ;
	requires x::node3<_, _, l, m, r> * l::tree2_3<n, Sl> * m::tree2_3<n, Sr> & n > 0 & r = null 
	ensures  x'::tree2_3<n+1, S> & x = x' & res = null & n > 0;
{
	node3 leaf = new node3(a, 0, null, null, null);		// creating a new leaf node
	if (x == null) {					// x is empty
		return leaf;
	}
	else {
		if (x.left == null) {				// x is a leaf
			if (x.maxl <= a) {
				node3 aux = new node3(x.maxl, a, x, leaf, null);
				x = null;	
				return aux;		
			}
			else {
				node3 aux = new node3(a, x.maxl, leaf, x, null);			
				x = null;
				return aux;
			}
		}
		else {						// x is an internal node
			node3 tmp1, tmp2;
			if(a < x.maxl) {			// we have to insert in the left substree 
				return insert_left(x, a, 1);
			}
			else {
				if(a < x.maxm) return insert_middle(x, a);
				else {
					if(x.right == null) return insert_middle(x, a);
					else return insert_right(x, a);
				}	
			}
		}
	}
}
	


