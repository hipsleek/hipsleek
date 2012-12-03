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
HeapPred G3(node a, node b,node c).

lseg<p> == self=p 
  or self::node<_,q>*q::lseg<p>
 inv true;

void append(ref node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;

*************************************
*******relational assumption ********
*************************************
[ G1(x,y)&true --> x::node<val_57_528',next_57_529'>@M * 
  HP_545(next_57_529',y)&true,
 HP_545(t_22',y)&t_22'!=null --> G1(t_22',y)&true,
 HP_545(next_59_557,y) * x'::node<val_57_550,y>@M&x=x' & 
  next_59_557=null --> G3(x',x,y)&true,
 G3(t_570,t_567,y) * x'::node<val_57_552,t_570>@M&t_567!=null & 
  x=x' --> G3(x',x,y) * HP_571(t_567)&true]
*************************************

*************************************
*******relational definition ********
*************************************
[ G3(x_581,x_582,y_583) ::= x_581::node<val_57_550,y_583_584>@M * HP_585(y_583_584,x_582,y_583) * 
HP_572(y_583)&x_581=x_582,
 G1(x_595,y_596) ::= x_595::node<val_57_528',next_57_529'>@M * HP_597(next_57_529',y_596) * 
HP_572(y_596)&true,
 HP_585(y_583_584,x_594,y_583) ::= 
 y_583_584::node<val_57_550,y_583_592>@M * HP_585(y_583_592,t_567,y_583)&true
 or emp&y_583=y_583_584
 or HP_571(y_583_584)&true
 ,
 HP_597(next_57_529',y_596) ::= 
 next_57_529'::node<val_57_528',next_57_600>@M * HP_597(next_57_600,y_596)&
 true
 or emp&next_57_529'=null
 ,
 HP_571(t_567) ::= emp&t_567!=null]
*************************************



*/


  infer [G1,G3]
  requires G1(x,y)
  ensures G3(x',x,y);//'

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


