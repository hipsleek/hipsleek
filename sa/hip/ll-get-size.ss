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


/* return the tail of a singly linked list */
int get_size(node x)
  infer[H,G]
  requires H(x)
  ensures G(x);
{
	if(x==null) 
		return 0;
	else 
		return get_size(x.next) + 1;
}

/*


byhand:
H(x)
then-branch:
H(x) & x = null --> G(x)
else-branch
H(x) & x!=null 
for x.next H(x) & x!=null  -> x::node<_,b>
	state:  x::node<_,b> * HP_1(x,b) & x!=null
	constr: H(x) & x!=null --> x::node<_,b> * HP_1(x,b)
get-size call
	x::node<_,b> * HP_1(x,b) & x!=null --> H(b) --* G(b)
	state x::node<_,b> * HP_1(x,b) & x!=null * G(b)
	constr: x::node<_,b> * HP_1(x,b) & x!=nul --> H(b)
end: x::node<_,b> * HP_1(x,b) & x!=null * G(b) -> G(x)

constrs:
H(x) & x = null --> G(x)
H(x) & x!=null --> x::node<_,b> * HP_1(x,b)
x::node<_,b> * HP_1(x,b) & x!=null --> H(b)
x::node<_,b> & x!=null * G(b) -> G(x)

auto:
1.H(x)&x=null --> G(x)
2.H(x) & x!=null -->  x::node<val_25_535',next_25_536'> * HP_557(next_25_536',x)
3.HP_557(v_node_25_537',x) * x::node<val_25_564,v_node_25_537'> &x!=null --> H(v_node_25_537')
4.x::node<val_25_564,v_node_25_574> & x!=null --> G(x)

//4. loss infomation of v_node_25_574



*/


