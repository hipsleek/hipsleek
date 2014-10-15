data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred H4(node a).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b,node c).

ll<> == self=null
  or self::node<_,q>*q::ll<>
 inv true;

lseg<p> == self=p 
  or self::node<_,q>*q::lseg<p>
 inv true;

void append(ref node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;

ERROR : spurious HP_576<..>

 G2(x,y) ::= x::node<_,y_595>@M * y_595::lseg<y>[LHSCase] * 
    HP_576(y_595)&true,
 G1(x) ::= x::node<_,next_37_534'>@M * next_37_534'::ll[LHSCase]&true]


*/


  infer [G1,G2]
  requires G1(x)
  ensures G2(x',y);//'

{
    node t = x.next;
	if (t == null){
	      x.next = y;	
}
	else {
	      append(t, y);
              x.next=t;
}
}


