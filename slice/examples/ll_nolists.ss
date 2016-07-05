/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, r> * r::ll<m> & n = m + 1
	inv n >= 0;

/* append two singly linked lists */
void append(node x, node y)

	requires x::ll<n1> * y::ll<n2> & x != null
	ensures x::ll<n> & n = n1 + n2;

{
	if (x.next == null) {
		x.next = y;
	} else {
		append(x.next, y);
	}
}

/* return the first element of a singly linked list */
int ret_first(node x)

	requires x::ll<n> & x != null
	ensures true;
	
{
	return x.val;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n> & x != null
	ensures x::ll<n1> * res::ll<n2> & n1 = 1 & n2 = n - 1;
	
{
	node tmp = x.next;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<n1> * y::ll<n2> & x != null
	ensures x::ll<n> & n = n2 + 1;
	
{
	x.next = y;
}

/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<n1> & x != null
	ensures x::ll<n2> & n2 = 1;

{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n1> & n1 >= 2
	ensures res::ll<n2> & n2 = n1 - 2;
	
{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)

	requires x::ll<n1> & x != null
	ensures x::ll<n2> & n2 = n1 + 1;
	
{
	if (x.next == null) {
		x.next = new node(a, null);
	} else {
		insert(x.next, a);
	}
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)

	requires x::ll<n1> & n1 > a & a > 0 
	ensures x::ll<n2> & n2 = n1 - 1;

{
	if (a == 1) {
		x.next = x.next.next;
	} else {
		delete(x.next, a-1);
	}	
}

/* function to delete the node with value a in a singly linked list */
node delete_val(node x, int a)

	requires x::ll<n1>
	ensures res::ll<n2> & n2 <= n1;
	
{
	if (x == null) {
		return x;
	} else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete_val(x.next, a));
	}
}

/* function to create a singly linked list with a nodes */
node create_list(int a)

	requires a >= 0 
	ensures res::ll<n> & n = a;

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

	requires xs::ll<n1> * ys::ll<n2> 
	ensures ys'::ll<n> & n = n1 + n2 & xs' = null;

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
