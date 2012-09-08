/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).
HeapPred G4(node a, node b, node c, node d).

/* append two singly linked lists */
void append(node x, node y)
  infer[H1,H2,G3]
  requires H1(x)*H2(y)
  ensures G3(x,x',y);//'
{
	if (x.next == null) {
		assume false;
		x.next = y;
	} else {
		//assume false;
		append(x.next, y);
	}
}

/* return the first element of a singly linked list */
int ret_first(node x)
  infer[H]
  requires H(x)
  ensures true;
{
	return x.val;
}

/* return the tail of a singly linked list */
node get_next(node x)
	infer [H,G]
	requires H(x)
	ensures G(x,x');
{
	node tmp = x.next;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)
  infer[H1,H2,G1]
  requires H1(x)*H2(y)
  ensures G3(x,x',y);//'
{
	x.next = y;
}

/* function to set null the tail of a list */
void set_null(node x)
  infer [H,G]
  requires H(x)
  ensures G(x,x');

{
	x.next = null;
}

/* function to get the third element of a list */
node get_next_next(node x) 
  infer [H,G]
  requires H(x)
  ensures G(x,x');	
{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
  infer [H,G]
  requires H(x)
  ensures G(x,x');
{
	if (x.next == null) {
		x.next = new node(a, null);
	} else {
		insert(x.next, a);
	}
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
  infer [H,G]
  requires H(x)
  ensures G(x,x');
{
	if (a == 1) {
		x.next = x.next.next;
	} else {
		delete(x.next, a-1);
	}	
}

/* function to delete the node with value a in a singly linked list */
node delete_val(node x, int a)
  infer [H,G]
  requires H(x)
  ensures G(x,x');
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
  infer [H]
  requires true
  ensures H(res);
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
  infer[H1,H2,G1,G2]
  requires H1(x)*H2(y)
  ensures G1(x,x')*G2(y,y');
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
