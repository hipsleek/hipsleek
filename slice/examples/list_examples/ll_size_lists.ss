/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<n1, L1> == self = null & n1 = 0 & L1 = [||]
	or self::node<v, r> * r::ll<n2, L2> & n1 = n2 + 1 & L1 = v:::L2
	inv n1 >= 0 & len(L1) >= 0;

/* append two singly linked lists */
node append(node x, node y)

	requires x::ll<n1, L1> * y::ll<n2, L2>
	ensures res::ll<n, L> & n = n1 + n2 & L = app(L1, L2);

{
	if (x == null)
	   return y;
	else {
		x.next = append (x.next, y);
		return x;
	}
}

/* return the first element of a singly linked list */
int ret_first(node x)

	requires x::ll<n, L> & len(L)>0
	ensures res = head(L);
	
{
	return x.val;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n, L> & len(L) > 0
	ensures x::ll<n1, L1> * res::ll<n2, L2> & L1 = [|head(L)|] & L2 = tail(L) & n1 = 1 & n = n1 + n2;
	
{
	node tmp = x.next;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<n1, L1> * y::ll<n2, L2> & len(L1) > 0
	ensures x::ll<n, L> & L = app([|head(L1)|], L2) & n = 1 + n2;
	
{
	x.next = y;
}

/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<n, L5> & len(L5) > 0
	ensures x::ll<1, L6> & L6 = [|head(L5)|];

{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n1, L1> & len(L1) > 1
	ensures res::ll<n2, L2> & L2 = tail(tail(L1)) & n1 = n2 + 2;
	
{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
/*void insert(node x, int a)

	requires x::ll<n1, L1> & len(L1) > 0
	ensures x::ll<n2, L2> & L2 = app(L1, [|a|]) & n2 = n1 + 1;
	
{
	if (x.next == null) {
		x.next = new node(a, null);
	} else {
		insert(x.next, a);
	}
}*/

node insert(node x, int a)

	requires x::ll<n1, L1>
	ensures res::ll<n2, L2> & L2 = app(L1, [|a|]) & n2 = n1 + 1;
	
{
	if (x == null) {
	   //assume false;
	   return new node (a, null);
	}
	else {
		//assume false;
		x.next = insert (x.next, a);
		return x;
	}
}

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)

	requires x::ll<n1, L1> & len(L1) > a & a > 0 
	ensures x::ll<n2, L2> & len(L2) = len(L1) - 1 & n1 = 1 + n2; /* incomplete */

{
	if (a == 1) {
		x.next = x.next.next;
	} else {
		delete(x.next, a-1);
	}	
}

/* function to delete the node with value a in a singly linked list */
node delete_val(node x, int a)

	requires x::ll<n1, L1>
	ensures res::ll<n2, L2> &
					 ( a inlist L1 & len(L2) + 1 = len(L1) & n2 + 1 = n1
					 | a notinlist L1 & L1 = L2 & n1 = n2);
	
{
	if (x == null) {
		//assume false;
		return x;
	} else {
		
		if (x.val == a) {
			//assume false;
			return x.next;
		} else {
			assume false;
			return new node(x.val, delete_val(x.next, a));
		}
	}
}

/* function to create a singly linked list with a nodes */
node create_list(int a)

	requires a >= 0 
	ensures res::ll<n, L> & len(L) = a & n = a;

{
	if (a == 0) {
		return null;
	} else {
		a = a - 1;
		return new node (0, create_list(a));
	}
}

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)

	requires xs::ll<n1, L1> * ys::ll<n2, L2> 
	ensures ys'::ll<n, L> & L = app(rev(L1), L2) & xs' = null & n = n1 + n2;

{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse(xs, ys);
	}
}
