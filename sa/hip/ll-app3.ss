data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;


/*


  H3(r_588) * x'::node<val_35_561,r_588>&  v_node_35_576!=null 
    --> H3(x')&true,
  H2(y) * HP_553(v_node_35_570) * x'::node<val_35_559,y>&
  v_node_35_570=null 
    --> H3(x')&true,
  H2(y)&true --> H2(y)&true,
  HP_553(v_node_35_576)& v_node_35_576!=null --> H1(v_node_35_576)&true,
  H1(x)&true --> x::node<val_35_533',next_35_534'> * 
  HP_553(next_35_534')&true]


 HP_603(y) ::= 
   emp&y=H2_y_615
   or y::node<val_35_559,y_606> * HP_603(y_606)&true
 ,

 H2(y) ::= emp&y=H2_y_615,

 H1(x_609) ::= x_609::node<val_35_533',next_35_534'> * next_35_534'::ls[LHSCase]&true,
 H3(x_602) ::= x_602::node<val_35_559,y> * HP_603(y)&true]
 
 lvar H2_y_615
 requires x::ls<> & x!=null & y=H2_y_615
 ensures H3(x'); 

*/

void append(ref node x, node y)
  // requires x::ls<> * y::ls<> & x!=null
  // ensures x'::ls<>;
  infer [H1,H2,H3]
  requires H1(x)*H2(y)
  ensures H3(x');
{
	if (x.next == null){
	      x.next = y;	
}
	else {
	      node r=x.next;
	      append(r, y);
              x.next=r;
}
}

