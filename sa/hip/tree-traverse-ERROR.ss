data node2 {
	int val;
	node2 left;
	node2 right; 
}

HeapPred H(node2 a).
HeapPred H1(node2 a).
HeapPred G(node2 a, node2 b).


void foo(ref node2 x)
	infer[H,G]
	requires H(x)
	ensures G(x,x');
{
	if (x != null)
	{
		foo(x.left);
		foo(x.right);	
	}
}

/*CAN NOT RUN
Procedure foo$node2 FAIL-2

Exception Failure("Expect a node") Occurred!

Error(s) detected when checking procedure foo$node2
*/

