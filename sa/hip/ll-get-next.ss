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
node get_next(node x)
  infer[H,G]
  requires H(x)
  ensures G(x,res);//n>=1 & n=m+1
{
  node tmp = x.next;
  x.next = null;
  return tmp;
  dprint;
}

/*

dprint: sa/hip/ll-get-next.ss:25: ctx:  List of Failesc Context: [FEC(0, 1, 0 )]

  State:HP_551(tmp_19',x) * x'::node<val_22_560,next_23_539'>&x'=x & next_23_539'=null & v_node_24_540'=tmp_19' & res=v_node_24_540'

      Try HP_551(tmp_19',x) * x::node<val_22_560,next_23_539'>& next_23_539'=null & v_node_24_540'=tmp_19' & res=v_node_24_540' |- G(x,res)



H(x) --> x::node<_,b> * HP_1285(b,x)
HP_1285(b,x) * x::node<val_214_1294,next_215_914'> --> G(x,b)

normalize
H(x) --> x::node<_,b> * HP_1285(b)
HP_1285(b) * x::node<val_214_1294,next_215_914'> --> G(x,b)
//lost infomation

expect:
H(x) -> x::node<_,b> * H1(x,b)
x::node<_,b> * H1(x,b) & tem = b

x::node<_,b'> * H1(x,b) & tem = b * b' = null
 
x::node<_,b'> * H1(x,b) & tem = b * b' = null -> G(x,b)
normalize:

H(x) -> x::node<_,b> * H1(b)
x::node<_,b'> * H1(b) * b' = null -> G(x,b)

//should have null here

final?
H(x) -> x::node<_,b> 
x::node<_,null> -> G(x,b)

expect2:
H(x) -> x::node<_,b> * H1(x,b)
x::node<_,b> * H1(x,b) & tem = b

x'::node<_,null> * H1(x,b) & tem = b 
 
x'::node<_,null> * H1(x,b) & tem = b  -> G(x,b)
normalize:

H(x) -> x::node<_,b> * H1(x,b)
x'::node<_,null> * H1(x,b) -> G(x,b)


final?
H(x) -> x::node<_,b> 
x::node<_,b> -> G(x,b)


*** H(x) -> x::node<_,b> * H1(x,b) *** constrant on node and node next -> change node next***
*/

