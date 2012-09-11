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

/* function to set the tail of a list */
 void set_next(ref node x,ref node y)
  infer[H1,H2,G3]
  requires H1(x)*H2(y)
  ensures G3(x,x',y);//'
{
	x.next = y;
}


/*
 H1(x) * H2(y) --> x::node<val_24_615',next_24_616'> * HP_822(next_24_616',y,x)
 HP_822(next_24_826,y,x) * x::node<val_24_827,y> --> G3(x,x,y)
normalize:
H1(x) * H2(y) --> x::node<_,b> * HP_822(b,y)
HP_822(next_24_826,y) * x::node<val_24_827,y> --> G3(x,x,y)

by-hand
H(x) --> H1(b) *  x::node<_,b>

H1(y) *  x::node<_,y> --> G(x,x,y) 

final?
H(x) --> x::node<_,b>

x::node<_,y> --> G(x,x,y) 

//okie
*/
/* function to set null the tail of a list */
void set_null(ref node x)
  infer [H,G]
  requires H(x)
  ensures G(x,x');

{
	x.next = null;
}

/*
 H(x) --> x::node<_,b> * HP_831(b,null)
 HP_831(next_34_835,b) * x::node<_,b>&b=null --> G(x,x)
normallize
 H(x) --> x::node<_,b>
 x::node<_,b>&b=null --> G(x,x)

by hand

H(x) --> H1(b) * x::node<_,b>

H1(b) * x::node<_,b> * x'::node<_,null> --> G(x,x')

H(x) -->  x::node<_,b>

x::node<_,b> * x'::node<_,null> --> G(x,x')

????
x::node<_,b>
or
x::node<_, null>

*/

/* function to get the third element of a list */
node get_next_next(ref node x) 
  infer [H,G]
  requires H(x)
  ensures G(x,x');	
{
	return x.next.next;
}




/*
 H(x) --> x::node<_,b> * HP_758(b,x)
 HP_758(b,x) * x::node<_,b> --> b::node<_,c> * HP_76(c,x,b)
 x::node<_,b> *  HP_766(c,x,b) *  b::node<_,c> --> G(x,x)

normalize
 H(x) -->  x::node<_,b> * b::node<_,c> * HP_76(c) -> G(x,x)
 H(x) -->  x::node<_,b> * b::node<_,c>
 H(x) --> G(x,x)
(return c)

*/



/* function to insert a node in a singly linked list */
void insert(ref node x, int a)
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
void delete(ref node x, int a)
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
node delete_val(ref node x, int a)
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


