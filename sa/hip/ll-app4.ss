data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred H4(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;

void append(ref node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;
*/
/*

# H1(x)&true --> x::node<_,n> * HP_554(n)&true

 x::node<_,n> * HP_554(n) * H2(y) & n!=null
   |- H1(n) * H2(y)
 # H2(y)&true --> H2(y)&true,
 # HP_554(v)&v!=null --> H1(v)&true,

 x::node<_,r> * H3(r) * H4(y) & n!=null & x'=x
   |- H3(x') * H4(y)
 # H4(y)&true --> H4(y)&true,
 # H3(r) * x'::node<_,r>&v_node_36_577!=null --> H3(x')&true,

 # emp&true --> H4(y)&true,
 @@ where did this come from
 
 x::node<_,y> * HP_554(v) * H2(y) & v=null
   |- H3(x') * H4(y)
 # H2(y) * HP_554(v) * x'::node<_,y>& v=null 
   --> H3(x') * H4(y)&true,
 @@ can decompose further, as below:
 @@ H2(y) -> H4(y)
 @@ HP_554(v) & v=null -> emp
 @@ x'::node<_,y> -> H3(x') // where y is logical

*/
  infer [H1,H2,H3,H4]
  requires H1(x)*H2(y)
  ensures H3(x')*H4(y);//'
  /*
[ HP_606(y) ::= y::node<val_36_560,y_609> * HP_606(y_609)&true,
 H4(y) ::= emp&y=H4_y_617,
 H2(y) ::= emp&y=H4_y_617,
 H1(x_611) ::= x_611::node<val_36_534',next_36_535'> * next_36_535'::ls[LHSCase]&true,
 H3(x_605) ::= x_605::node<val_36_560,y> * HP_606(y)&true]
  */
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


