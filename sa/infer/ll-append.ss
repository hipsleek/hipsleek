/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

void append(node x, node y)
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/*
infer[H,G] H(x,y) |- H1(x,y,b) * x::node<_,b>

if:
case 1: H1(x,y,b) * x::node<_,b> & b = null

x.next = y: H1(x,y,b) * x::node<_,y> & b = null

post-cond: H1(x,y,b) * x::node<_,y> & b = null & x' = x & y' = y -> G(x,x',y,y')

if:
case 2: H1(x,y,b) * x::node<_,b> & b != null

recursive call: H1(x,y,b) * x::node<_,b> & b != null & x' = x & y' = y |- H(b,y') --* G(b, b', y', y'')
--> G(b, b', y0, y') * x::node<_,b> & b != null & x' = x & y0 = y
  with H1(x,y,b) * x::node<_,b> & b != null & y' = y |- H(b,y')

post-cond: G(b, b', y0, y') * x::node<_,b> & b != null & x' = x & y0 = y -> G(x,x',y,y')

H(x,y) -> H1(x,y,b) * x::node<_,b>
H1(x,y,b) * x::node<_,y> & b = null & x' = x & y' = y -> G(x,x',y,y')
H1(x,y,b) * x::node<_,b> & b != null & y' = y |- H(b,y')
G(b, b', y0, y') * x::node<_,b> & b != null & x' = x & y0 = y -> G(x,x',y,y')


*/




