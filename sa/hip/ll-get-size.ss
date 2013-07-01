data node {
	int val;
	node next
}

HeapPred H(node a).
HeapPred G(node a).



/* return the tail of a singly linked list */
int get_size(node x)
  infer[H,G]
  requires H(x)
  ensures G(x);
{
	if(x==null) 
		return 0;
	else {
      int a = get_size(x.next);
      return  a+ 1;
    }
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
H(x) & x=null--> G(x)
H(x) & x!=null) --> x::node<val_25_536',next_25_537'> * HP_557(next_25_537',x)
HP_557(v_node_25_538',x) * x::node<val_25_564,v_node_25_538'> & x!=null --> H(v_node_25_538')
x::node<val_25_564,v_node_25_574> * G(v_node_25_574) & x!=null --> G(x)

//MATCH
H(x)::  x=null or x::node<val_25_536',next_25_537'> * H(next_25_537')				//ll
G(x)::  emp & x=null or x::node<val_25_564,v_node_25_574> * G(v_node_25_574) & x!=null		//ll
HP_557(v_node_25_538')::  H(v_node_25_538')							//do not need

//SUCCESS




*/


